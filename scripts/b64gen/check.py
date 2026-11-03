#!/usr/bin/env python3
# scripts/b64gen/check.py -- regenerate every generated B64 proof file into a
# temporary directory and compare it byte for byte with the committed one.
#   python3 scripts/b64gen/check.py           guard (exit 1 on drift)
#   python3 scripts/b64gen/check.py --write   regenerate in place
# AI assistance disclosure: AI-drafted; human review pending.
import os, shutil, subprocess, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
G = os.path.join(ROOT, "scripts", "b64gen")
FILES = ["B64_SinPoly.v", "B64_Sin.v", "B64_CosPoly.v", "B64_Cos.v",
         "B64_FresnelPolyC.v", "B64_FresnelPolyS.v", "B64_FresnelPoly.v", "B64_Fresnel.v"]

def run(script, *args):
    subprocess.run([sys.executable, "-I", os.path.join(G, script), *args],
                   check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def main():
    t = tempfile.mkdtemp()
    try:
        p = lambda n: os.path.join(t, n)
        run("gen_sinpoly.py", p("B64_SinPoly.v"))
        run("gen_sin.py", p("B64_Sin.v"), p("B64_SinPoly.v"))
        run("gen_cospoly.py", p("B64_CosPoly.v"))
        run("gen_cos.py", p("B64_Cos.v"), p("B64_CosPoly.v"), p("B64_Sin.v"))
        run("gen_fresnelpoly.py", p("B64_FresnelPoly.v"), p("info.json"))
        run("gen_fresnel.py", p("B64_Fresnel.v"), p("info.json"))
        bad = []
        for f in FILES:
            committed = os.path.join(ROOT, "theories-flocq", f)
            if "--write" in sys.argv:
                shutil.copyfile(p(f), committed)
            elif open(p(f), "rb").read() != open(committed, "rb").read():
                bad.append(f)
        if bad:
            print("[b64gen] DRIFT: generated != committed for " + ", ".join(bad))
            print("  regenerate with: python3 scripts/b64gen/check.py --write")
            return 1
        print("[b64gen] OK: %d generated proof files reproduce byte for byte" % len(FILES))
        return 0
    finally:
        shutil.rmtree(t)

if __name__ == "__main__":
    sys.exit(main())
