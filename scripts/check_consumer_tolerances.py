#!/usr/bin/env python3
# scripts/check_consumer_tolerances.py -- guard for oracle/fixtures/consumer-tolerances.json.
#   * valid JSON with the expected schema and status vocabulary;
#   * every listed lemma exists in theories*/ (pending_lemmas are not checked);
#   * a "blocked" record names at least one unblock_when item;
#   * every inventory id appears in docs/consumer-switch-decisions.tsv.
# Build-independent (no .vo).  Exit 0 ok, 1 violation.
# AI assistance disclosure: AI-drafted; human review pending.
import glob, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATUS = {"decided", "blocked", "recorded"}
KEYS = {"id", "inventory", "consumer", "status", "decision", "tolerance",
        "lemmas", "pending_lemmas", "unblock_when", "stop_conditions"}


def main():
    errs = []
    path = os.path.join(ROOT, "oracle", "fixtures", "consumer-tolerances.json")
    try:
        data = json.load(open(path, encoding="utf-8"))
    except Exception as ex:
        print(f"[consumer-tolerances] cannot read {path}: {ex}")
        return 1
    if data.get("schema") != "consumer-tolerances/1":
        errs.append("schema must be consumer-tolerances/1")
    src = ""
    for f in glob.glob(os.path.join(ROOT, "theories*", "*.v")):
        src += open(f, encoding="utf-8", errors="replace").read() + "\n"
    tsv = open(os.path.join(ROOT, "docs", "consumer-switch-decisions.tsv"),
               encoding="utf-8").read()
    ids = set()
    for c in data.get("consumers", []):
        cid = c.get("id", "?")
        missing = KEYS - set(c)
        if missing:
            errs.append(f"{cid}: missing keys {sorted(missing)}")
            continue
        if cid in ids:
            errs.append(f"{cid}: duplicate id")
        ids.add(cid)
        if c["status"] not in STATUS:
            errs.append(f"{cid}: status {c['status']!r} not in {sorted(STATUS)}")
        if c["status"] == "blocked" and not c["unblock_when"]:
            errs.append(f"{cid}: blocked without unblock_when")
        if not isinstance(c["tolerance"], dict) or "kind" not in c["tolerance"]:
            errs.append(f"{cid}: tolerance must be an object with a kind")
        for lem in c["lemmas"]:
            if not re.search(r"\b(Lemma|Theorem|Corollary|Definition)\s+" + re.escape(lem) + r"\b", src):
                errs.append(f"{cid}: lemma {lem} not found in theories*/")
        if not re.search(r"(^|\t)" + re.escape(c["inventory"]) + r"(\t|\s)", tsv):
            errs.append(f"{cid}: inventory {c['inventory']} not in consumer-switch-decisions.tsv")
    if errs:
        print("[consumer-tolerances] FAIL")
        for e in errs:
            print("  " + e)
        return 1
    print(f"[consumer-tolerances] OK: {len(ids)} consumer record(s), lemmas resolve")
    return 0


if __name__ == "__main__":
    sys.exit(main())
