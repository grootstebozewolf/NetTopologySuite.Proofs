// CLI: WKT → tagged CST → SHC bag | Intake Decline.
// Upstream of oracle/driver.ml (ADR-0006). No new oracle keyword.
// Assisted-by: Cursor Grok 4.6. claimId: none (tools).

using System.Text;
using Antlr4.Runtime;
using Nts.Proofs.Intake.Gen;

namespace Nts.Proofs.Intake;

static class Program
{
    static int Main(string[] args)
    {
        bool strict = false;
        var rest = new List<string>();
        foreach (var a in args)
        {
            if (a == "--strict") strict = true;
            else rest.Add(a);
        }
        var wkts = new List<string>();
        if (rest.Count == 0)
            wkts.AddRange(ReadStdinLines());
        else if (rest[0] == "--file" && rest.Count >= 2)
            wkts.AddRange(NonBlank(File.ReadAllLines(rest[1], Encoding.UTF8)));
        else
            wkts.Add(string.Join(' ', rest));
        if (wkts.Count == 0)
        {
            Console.WriteLine(IntakeResult.OfDecline(Reason.ID_Empty).Wire());
            return 2;
        }
        int rc = 0;
        foreach (var wkt in wkts)
        {
            var r = Intake(wkt, strict);
            Console.WriteLine(r.Wire());
            if (!r.IsBag)
                rc = 3;
        }
        return rc;
    }

    internal static IntakeResult Intake(string wkt, bool strict = false)
    {
        var errors = new BailErrors();
        var lexer = new wktLexer(CharStreams.fromString(wkt));
        lexer.RemoveErrorListeners();
        lexer.AddErrorListener(errors);
        var parser = new wktParser(new CommonTokenStream(lexer));
        parser.RemoveErrorListeners();
        parser.AddErrorListener(errors);
        var tree = parser.file_();
        if (errors.Failed || parser.NumberOfSyntaxErrors > 0)
            return IntakeResult.OfDecline(Reason.ID_ParseFail);
        var mode = strict ? IntakeMode.Strict : IntakeMode.Lenient;
        return new IntakeVisitor(mode).Visit(tree);
    }

    static List<string> ReadStdinLines()
    {
        using var stdin = Console.OpenStandardInput();
        using var reader = new StreamReader(stdin, Encoding.UTF8);
        return NonBlank(reader.ReadToEnd().Replace("\r\n", "\n").Split('\n'));
    }

    static List<string> NonBlank(IEnumerable<string> lines)
    {
        var outList = new List<string>();
        foreach (var line in lines)
        {
            string t = line.Trim();
            if (t.Length > 0 && !t.StartsWith('#'))
                outList.Add(t);
        }
        return outList;
    }

    sealed class BailErrors : BaseErrorListener, IAntlrErrorListener<int>
    {
        public bool Failed;

        public override void SyntaxError(
            TextWriter output, IRecognizer recognizer, IToken offendingSymbol,
            int line, int charPositionInLine, string msg, RecognitionException e)
        {
            Failed = true;
        }

        public void SyntaxError(
            TextWriter output, IRecognizer recognizer, int offendingSymbol,
            int line, int charPositionInLine, string msg, RecognitionException e)
        {
            Failed = true;
        }
    }
}
