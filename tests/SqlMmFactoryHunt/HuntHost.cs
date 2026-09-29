// SqlMmFactoryHunt — drive the Java ST4 factory and C# WktIntakeWalker via Process.
// Factory stays Java; intake is tools/WktIntakeWalker (dotnet run / built exe).
// Assisted-by: Cursor Grok 4.6. claimId: none (tools).

using System.Diagnostics;
using System.Text;

static class HuntHost
{
    internal static string RepoRoot { get; private set; } = "";
    internal static string FactoryCp { get; private set; } = "";
    internal static string IntakeCli { get; private set; } = "";
    internal static string Templates { get; private set; } = "";
    internal static string DotNet { get; private set; } = "";

    static string Sep => Path.PathSeparator.ToString();

    internal static void EnsureReady()
    {
        RepoRoot = FindRepoRoot();
        DotNet = FindDotNet();
        Templates = Environment.GetEnvironmentVariable("SQLMM_FACTORY_TEMPLATES")
            ?? Path.Combine(RepoRoot, "tools", "SqlMmExampleFactory", "templates");
        FactoryCp = Environment.GetEnvironmentVariable("SQLMM_FACTORY_CP") ?? "";
        IntakeCli = FirstNonEmpty(
            Environment.GetEnvironmentVariable("SQLMM_INTAKE"),
            Environment.GetEnvironmentVariable("SQLMM_INTAKE_DLL"));
        if (string.IsNullOrWhiteSpace(FactoryCp) || string.IsNullOrWhiteSpace(IntakeCli))
            Build();
        if (string.IsNullOrWhiteSpace(FactoryCp) || string.IsNullOrWhiteSpace(IntakeCli))
            throw new InvalidOperationException("SQLMM_FACTORY_CP / SQLMM_INTAKE unset after build");
    }

    static string FirstNonEmpty(params string?[] values)
    {
        foreach (var v in values)
        {
            if (!string.IsNullOrWhiteSpace(v))
                return v;
        }
        return "";
    }

    static string FindRepoRoot()
    {
        var env = Environment.GetEnvironmentVariable("SQLMM_REPO");
        if (!string.IsNullOrWhiteSpace(env) && LooksLikeRepo(env))
            return Path.GetFullPath(env);
        foreach (var start in new[] { Directory.GetCurrentDirectory(), AppContext.BaseDirectory })
        {
            var d = new DirectoryInfo(start);
            while (d != null)
            {
                if (LooksLikeRepo(d.FullName))
                    return d.FullName;
                d = d.Parent;
            }
        }
        throw new DirectoryNotFoundException(
            "cannot find repo root (tools/SqlMmExampleFactory + tools/WktIntakeWalker)");
    }

    static bool LooksLikeRepo(string root) =>
        Directory.Exists(Path.Combine(root, "tools", "SqlMmExampleFactory"))
        && File.Exists(Path.Combine(root, "tools", "WktIntakeWalker", "WktIntakeWalker.csproj"));

    static void Build()
    {
        string factory = Path.Combine(RepoRoot, "tools", "SqlMmExampleFactory");
        string intake = Path.Combine(RepoRoot, "tools", "WktIntakeWalker");

        if (string.IsNullOrWhiteSpace(FactoryCp))
        {
            RunBash(Path.Combine(factory, "generate.sh"), factory);
            string st4Ver = Environment.GetEnvironmentVariable("ST4_VER") ?? "4.3.4";
            string a3Ver = Environment.GetEnvironmentVariable("ANTLR3_RUNTIME_VER") ?? "3.5.3";
            string factoryLib = Path.Combine(factory, ".lib");
            string factoryOut = Path.Combine(factory, ".build");
            string factoryCpJars = string.Join(Sep,
                Path.Combine(factoryLib, $"ST4-{st4Ver}.jar"),
                Path.Combine(factoryLib, $"antlr-runtime-{a3Ver}.jar"));
            Javac(Path.Combine(factory, "java"), factoryOut, factoryCpJars);
            FactoryCp = factoryOut + Sep + factoryCpJars;
            Templates = Path.Combine(factory, "templates");
        }

        if (string.IsNullOrWhiteSpace(IntakeCli))
        {
            RunPwsh(Path.Combine(intake, "generate.ps1"), intake);
            var (rc, _, err) = Run(DotNet, ["build", Path.Combine(intake, "WktIntakeWalker.csproj"), "--nologo"], intake);
            if (rc != 0)
                throw new InvalidOperationException($"dotnet build WktIntakeWalker failed ({rc}): {err}");
            IntakeCli = ResolveIntakeCli(intake);
        }
    }

    static string ResolveIntakeCli(string intake)
    {
        foreach (var candidate in new[]
        {
            Path.Combine(intake, "bin", "Debug", "net10.0", "WktIntakeWalker.dll"),
            Path.Combine(intake, "bin", "Release", "net10.0", "WktIntakeWalker.dll"),
            Path.Combine(intake, "bin", "Debug", "net10.0", "WktIntakeWalker"),
            Path.Combine(intake, "bin", "Debug", "net10.0", "WktIntakeWalker.exe"),
        })
        {
            if (File.Exists(candidate))
                return candidate;
        }
        throw new FileNotFoundException($"WktIntakeWalker CLI missing under {intake}/bin after build");
    }

    static void Javac(string javaDir, string outDir, string cp)
    {
        Directory.CreateDirectory(outDir);
        string list = Path.Combine(outDir, "sources.list");
        File.WriteAllLines(list, Directory.GetFiles(javaDir, "*.java", SearchOption.AllDirectories));
        var (rc, _, err) = Run("javac", ["-cp", cp, "-d", outDir, "@" + list], outDir);
        if (rc != 0)
            throw new InvalidOperationException($"javac failed ({rc}): {err}");
    }

    static void RunBash(string script, string cwd)
    {
        if (!File.Exists(script))
            throw new FileNotFoundException(script);
        var (rc, _, err) = Run(FindBash(), [script], cwd);
        if (rc != 0)
            throw new InvalidOperationException($"{script} failed ({rc}): {err}");
    }

    static void RunPwsh(string script, string cwd)
    {
        if (!File.Exists(script))
            throw new FileNotFoundException(script);
        var (rc, _, err) = Run(FindPwsh(), ["-NoProfile", "-File", script], cwd);
        if (rc != 0)
            throw new InvalidOperationException($"{script} failed ({rc}): {err}");
    }

    static string FindBash()
    {
        if (OperatingSystem.IsWindows())
        {
            foreach (var c in new[]
            {
                @"C:\Program Files\Git\bin\bash.exe",
                @"C:\Windows\System32\bash.exe",
            })
            {
                if (File.Exists(c)) return c;
            }
        }
        return "bash";
    }

    static string FindPwsh()
    {
        if (OperatingSystem.IsWindows())
        {
            if (!string.IsNullOrEmpty(Which("pwsh")))
                return "pwsh";
            return "powershell";
        }
        foreach (var c in new[]
        {
            "pwsh",
            Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".local", "pwsh", "pwsh"),
            "/usr/bin/pwsh",
        })
        {
            if (c == "pwsh" && !string.IsNullOrEmpty(Which("pwsh")))
                return "pwsh";
            if (c != "pwsh" && File.Exists(c))
                return c;
        }
        throw new FileNotFoundException("pwsh not found (needed for tools/WktIntakeWalker/generate.ps1)");
    }

    static string FindDotNet()
    {
        if (!string.IsNullOrEmpty(Which("dotnet")))
            return "dotnet";
        foreach (var c in new[]
        {
            Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".dotnet", "dotnet"),
            "/usr/share/dotnet/dotnet",
        })
        {
            if (File.Exists(c))
            {
                string root = Path.GetDirectoryName(c)!;
                Environment.SetEnvironmentVariable("DOTNET_ROOT", root);
                string path = Environment.GetEnvironmentVariable("PATH") ?? "";
                Environment.SetEnvironmentVariable("PATH", root + Path.PathSeparator + path);
                return c;
            }
        }
        throw new FileNotFoundException("dotnet not found (needed for C# WktIntakeWalker)");
    }

    static string Which(string name)
    {
        var path = Environment.GetEnvironmentVariable("PATH") ?? "";
        foreach (var dir in path.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries))
        {
            var candidate = Path.Combine(dir, name);
            if (File.Exists(candidate))
                return candidate;
            if (OperatingSystem.IsWindows() && File.Exists(candidate + ".exe"))
                return candidate + ".exe";
        }
        return "";
    }

    internal static (int Rc, string Stdout, string Stderr) FactoryId(string exampleId) =>
        RunJava(FactoryCp, "org.nts.proofs.factory.Main", [exampleId], stdin: null, factoryEnv: true);

    internal static (int Rc, string Stdout, string Stderr) FactoryStdin(string model) =>
        RunJava(FactoryCp, "org.nts.proofs.factory.Main", ["--stdin"], stdin: model, factoryEnv: true);

    internal static (int Rc, string Stdout, string Stderr) FactoryList() =>
        RunJava(FactoryCp, "org.nts.proofs.factory.Main", ["--list"], stdin: null, factoryEnv: true);

    internal static (int Rc, string Stdout, string Stderr) Intake(string wkt, bool strict = false)
    {
        if (string.IsNullOrWhiteSpace(IntakeCli))
            throw new InvalidOperationException("SQLMM_INTAKE unset");
        var tail = strict ? new List<string> { "--strict", wkt } : new List<string> { wkt };
        if (IntakeCli.EndsWith(".dll", StringComparison.OrdinalIgnoreCase)
            || IntakeCli.EndsWith(".csproj", StringComparison.OrdinalIgnoreCase))
        {
            var argv = IntakeCli.EndsWith(".csproj", StringComparison.OrdinalIgnoreCase)
                ? new List<string> { "run", "--project", IntakeCli, "--" }
                : new List<string> { IntakeCli };
            argv.AddRange(tail);
            return Run(DotNet, argv, RepoRoot);
        }
        return Run(IntakeCli, tail, RepoRoot);
    }

    static (int Rc, string Stdout, string Stderr) RunJava(
        string cp, string main, string[] args, string? stdin, bool factoryEnv)
    {
        var argv = new List<string> { "-cp", cp, main };
        argv.AddRange(args);
        return Run("java", argv, RepoRoot, stdin, factoryEnv);
    }

    static (int Rc, string Stdout, string Stderr) Run(
        string file, IReadOnlyList<string> args, string cwd, string? stdin = null, bool factoryEnv = false)
    {
        var psi = new ProcessStartInfo
        {
            FileName = file,
            WorkingDirectory = cwd,
            RedirectStandardInput = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            StandardOutputEncoding = Encoding.UTF8,
            StandardErrorEncoding = Encoding.UTF8,
        };
        foreach (var a in args)
            psi.ArgumentList.Add(a);
        if (factoryEnv)
            psi.Environment["SQLMM_FACTORY_TEMPLATES"] = Templates;
        using var p = Process.Start(psi) ?? throw new InvalidOperationException($"failed to start {file}");
        if (stdin != null)
            p.StandardInput.Write(stdin);
        p.StandardInput.Close();
        string stdout = p.StandardOutput.ReadToEnd();
        string stderr = p.StandardError.ReadToEnd();
        if (!p.WaitForExit(20000))
            throw new TimeoutException($"{file} timeout");
        return (p.ExitCode, stdout, stderr);
    }

    internal static Dictionary<string, string> ParseFields(string stdout)
    {
        var outDict = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var line in stdout.Split('\n'))
        {
            int eq = line.IndexOf('=');
            if (eq <= 0) continue;
            outDict[line[..eq].Trim()] = line[(eq + 1)..].TrimEnd('\r');
        }
        return outDict;
    }

    internal static IReadOnlyList<string> CatalogIds()
    {
        var (rc, stdout, err) = FactoryList();
        if (rc != 0)
            throw new InvalidOperationException($"factory --list failed: {err}");
        return stdout.Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
    }
}
