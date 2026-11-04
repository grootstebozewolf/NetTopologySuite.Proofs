// S10 conformance harness, Java side: replays the shared contract corpus
// (tests/B64SinConformance/corpus.py: DIR/<MODE>.in and the extracted
// oracle's answers DIR/<MODE>.out) against B64Trig and compares output
// BITS and decisions, exactly as the C# harness (Program.cs) does.
// Build and run:
//   javac -d BUILD tests/B64SinConformance/java/nts/proofs/numerics/*.java
//   java -cp BUILD nts.proofs.numerics.Conformance DIR
// Exit 0 = every mode bit-identical.
// AI assistance disclosure: AI-drafted; human review pending.
package nts.proofs.numerics;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.function.Function;

public final class Conformance {
    private Conformance() { }

    private static String h(double v) {
        return String.format("%016x", Double.doubleToRawLongBits(v));
    }

    private static double d(String s) {
        return Double.longBitsToDouble(Long.parseUnsignedLong(s, 16));
    }

    private record Mode(String name, Function<String[], String> eval) { }

    public static void main(String[] args) throws IOException {
        if (args.length < 1) {
            System.err.println("usage: java -cp BUILD nts.proofs.numerics.Conformance CORPUS_DIR");
            System.exit(2);
        }
        Path dir = Path.of(args[0]);
        List<Mode> modes = List.of(
            new Mode("B64_SIN", f -> { double x = d(f[0]); return B64Trig.accept(x) ? h(B64Trig.sin(x)) : "DECLINE"; }),
            new Mode("B64_COS", f -> { double x = d(f[0]); return B64Trig.accept(x) ? h(B64Trig.cos(x)) : "DECLINE"; }),
            new Mode("B64_ARC_PT", f -> {
                double cx = d(f[0]), cy = d(f[1]), r = d(f[2]), t = d(f[3]);
                return B64Trig.arcAccept(cx, cy, r, t)
                    ? h(B64Trig.arcX(cx, r, t)) + " " + h(B64Trig.arcY(cy, r, t)) : "DECLINE";
            }),
            new Mode("B64_FRESNEL", f -> {
                double x = d(f[0]);
                return B64Trig.fresnelAccept(x)
                    ? h(B64Trig.fresnelC(x)) + " " + h(B64Trig.fresnelS(x)) : "DECLINE_FRESNEL_RANGE";
            }),
            new Mode("B64_CLOTHOID", f -> {
                double a = d(f[0]), s = d(f[1]);
                boolean neg = f[2].equals("1");
                return B64Trig.clothoidAccept(a, s)
                    ? h(B64Trig.clothoidIcos(a, s)) + " " + h(B64Trig.clothoidIsin(neg, a, s))
                    : "DECLINE_FRESNEL_RANGE";
            }),
            new Mode("B64_SEG_G", f -> B64Trig.segGOutcome(d(f[0]))));

        int totalBug = 0;
        for (Mode m : modes) {
            List<String> ins = Files.readAllLines(dir.resolve(m.name() + ".in")).stream()
                .filter(l -> !l.isEmpty()).toList();
            List<String> outs = Files.readAllLines(dir.resolve(m.name() + ".out")).stream()
                .filter(l -> !l.isEmpty()).toList();
            int ok = 0, bug = 0, declined = 0;
            if (ins.size() != outs.size()) {
                System.out.printf("!! %s: %d inputs but %d oracle answers%n", m.name(), ins.size(), outs.size());
                bug = 1;
            } else {
                for (int i = 0; i < ins.size(); i++) {
                    String mine = m.eval().apply(ins.get(i).split(" "));
                    String theirs = outs.get(i).trim();
                    if (mine.equals(theirs)) {
                        ok++;
                        if (mine.startsWith("DECLINE")) declined++;
                    } else if (++bug <= 10) {
                        System.out.printf("!! %s in=[%s] java=%s oracle=%s%n", m.name(), ins.get(i), mine, theirs);
                    }
                }
            }
            System.out.printf("# %s cases %d, of which declined %d%n", m.name(), ins.size(), declined);
            System.out.printf("SUMMARY %s ok=%d warn=0 bug=%d%n", m.name(), ok, bug);
            totalBug += bug;
        }
        System.exit(totalBug == 0 ? 0 : 1);
    }
}
