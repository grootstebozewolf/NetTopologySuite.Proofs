// Thin Cake entry — house style (.NET / PowerShell / Cake / RGR).
// Targets: WktIntakeWalker, SqlMmFactoryHunt, SqlMmWktAngleHunt.
// claimId: none (tools). No new ADR-0006 keyword.
// Assisted-by: Cursor Grok 4.6.

var target = Argument("target", "Default");
var budget = Argument("budget", 300);
var seed = Argument("seed", 42);
var pinsOnly = HasArgument("pins-only") || HasArgument("pinsOnly");

Task("WktIntakeWalker")
    .Does(() =>
{
    var script = MakeAbsolute(File("./tools/WktIntakeWalker/smoke.ps1"));
    if (!FileExists(script))
        throw new CakeException($"missing {script}");

    var shell = FindPwsh();
    var args = new ProcessArgumentBuilder()
        .Append("-NoProfile")
        .Append("-File").AppendQuoted(script.FullPath);

    var exit = StartProcess(shell, new ProcessSettings { Arguments = args });
    if (exit != 0)
        throw new CakeException($"WktIntakeWalker exited {exit}");
});

Task("SqlMmFactoryHunt")
    .Does(() =>
{
    var script = MakeAbsolute(File("./tests/SqlMmFactoryHunt/hunt.ps1"));
    if (!FileExists(script))
        throw new CakeException($"missing {script}");

    var shell = FindPwsh();
    var args = new ProcessArgumentBuilder()
        .Append("-NoProfile")
        .Append("-File").AppendQuoted(script.FullPath)
        .Append("-Budget").Append(budget.ToString())
        .Append("-Seed").Append(seed.ToString());
    if (pinsOnly)
        args.Append("-PinsOnly");

    var exit = StartProcess(shell, new ProcessSettings { Arguments = args });
    if (exit != 0)
        throw new CakeException($"SqlMmFactoryHunt exited {exit}");
});

Task("SqlMmWktAngleHunt")
    .Does(() =>
{
    var script = MakeAbsolute(File("./tests/SqlMmWktAngleHunt/hunt.ps1"));
    if (!FileExists(script))
        throw new CakeException($"missing {script}");

    var shell = FindPwsh();
    var args = new ProcessArgumentBuilder()
        .Append("-NoProfile")
        .Append("-File").AppendQuoted(script.FullPath);

    var exit = StartProcess(shell, new ProcessSettings { Arguments = args });
    if (exit != 0)
        throw new CakeException($"SqlMmWktAngleHunt exited {exit}");
});

Task("Default")
    .Does(() =>
{
    Information("Targets: WktIntakeWalker, SqlMmFactoryHunt, SqlMmWktAngleHunt");
    Information("  pwsh ./tools/WktIntakeWalker/smoke.ps1");
    Information("  dotnet cake --target=WktIntakeWalker");
    Information("  dotnet run --project tools/WktIntakeWalker -- \"LINESTRING (0 0, 2 0)\"");
    Information("  dotnet cake --target=SqlMmFactoryHunt --budget=300 --seed=42");
    Information("  pwsh ./tests/SqlMmFactoryHunt/hunt.ps1 -Budget 300 -Seed 42");
    Information("  dotnet run --project tests/SqlMmFactoryHunt -- --budget 300 --seed 42");
    Information("  pwsh ./tests/SqlMmWktAngleHunt/hunt.ps1");
    Information("  dotnet cake --target=SqlMmWktAngleHunt");
});

RunTarget(target);

string FindPwsh()
{
    if (IsRunningOnWindows())
    {
        if (!string.IsNullOrEmpty(Which("pwsh")))
            return "pwsh";
        return "powershell";
    }
    foreach (var c in new[]
    {
        "pwsh",
        System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".local/pwsh/pwsh"),
        "/usr/bin/pwsh",
    })
    {
        if (c == "pwsh" && !string.IsNullOrEmpty(Which("pwsh")))
            return "pwsh";
        if (c != "pwsh" && FileExists(c))
            return c;
    }
    throw new CakeException("pwsh not found. Install PowerShell 7, or run smoke.ps1 / hunt.ps1 directly.");
}

string Which(string name)
{
    var path = Environment.GetEnvironmentVariable("PATH") ?? "";
    foreach (var dir in path.Split(System.IO.Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries))
    {
        var candidate = System.IO.Path.Combine(dir, name);
        if (FileExists(candidate))
            return candidate;
        if (IsRunningOnWindows() && FileExists(candidate + ".exe"))
            return candidate + ".exe";
    }
    return "";
}
