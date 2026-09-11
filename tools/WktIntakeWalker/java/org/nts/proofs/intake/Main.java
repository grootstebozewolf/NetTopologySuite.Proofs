package org.nts.proofs.intake;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.nts.proofs.intake.IntakeResult.Reason;
import org.nts.proofs.intake.gen.wktLexer;
import org.nts.proofs.intake.gen.wktParser;

/**
 * CLI: WKT → tagged CST → SHC bag | Intake Decline.
 * Upstream of oracle/driver.ml (ADR-0006). No new oracle keyword.
 */
public final class Main {
    public static void main(String[] args) throws Exception {
        List<String> wkts = new ArrayList<>();
        if (args.length == 0) {
            wkts.addAll(readStdinLines());
        } else if ("--file".equals(args[0]) && args.length >= 2) {
            wkts.addAll(nonBlank(Files.readAllLines(Path.of(args[1]), StandardCharsets.UTF_8)));
        } else {
            wkts.add(String.join(" ", args));
        }
        if (wkts.isEmpty()) {
            System.out.println(IntakeResult.decline(Reason.ID_Empty).wire());
            System.exit(2);
        }
        int rc = 0;
        for (String wkt : wkts) {
            IntakeResult r = intake(wkt);
            System.out.println(r.wire());
            if (!r.isBag()) {
                rc = 3;
            }
        }
        System.exit(rc);
    }

    public static IntakeResult intake(String wkt) {
        BailErrors errors = new BailErrors();
        wktLexer lexer = new wktLexer(CharStreams.fromString(wkt));
        lexer.removeErrorListeners();
        lexer.addErrorListener(errors);
        wktParser parser = new wktParser(new CommonTokenStream(lexer));
        parser.removeErrorListeners();
        parser.addErrorListener(errors);
        wktParser.File_Context tree = parser.file_();
        if (errors.failed || parser.getNumberOfSyntaxErrors() > 0) {
            return IntakeResult.decline(Reason.ID_ParseFail);
        }
        return new IntakeVisitor().visit(tree);
    }

    private static List<String> readStdinLines() throws Exception {
        return nonBlank(new String(System.in.readAllBytes(), StandardCharsets.UTF_8).lines().toList());
    }

    private static List<String> nonBlank(List<String> lines) {
        List<String> out = new ArrayList<>();
        for (String line : lines) {
            String t = line.trim();
            if (!t.isEmpty() && !t.startsWith("#")) {
                out.add(t);
            }
        }
        return out;
    }

    private static final class BailErrors extends BaseErrorListener {
        boolean failed;

        @Override
        public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol,
                int line, int charPositionInLine, String msg, RecognitionException e) {
            failed = true;
        }
    }
}
