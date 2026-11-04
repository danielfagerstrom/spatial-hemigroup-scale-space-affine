# Export note: 1 file path(s) on the author's machine were replaced by <local path> in this public copy; nothing else was changed.
import re, sys, collections
base = r"<local path>"
rep = open(base + "/lean-axiom-report.txt", encoding="utf-8").read()
# parse report
entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", rep, re.S)
report = {}
for name, ax in entries:
    axs = [a.strip() for a in ax.replace("\n", " ").split(",") if a.strip()]
    short = name.replace("AffineHemigroup.", "")
    report[short] = axs
print("declarations in report:", len(entries), "distinct:", len(report))
logical = {"propext", "Classical.choice", "Quot.sound"}
nine = {"AffineHemigroup." + n for n in [
 "density_of_integrable_charFun", "sato_polar_criterion", "levy_khintchine_exists",
 "levy_khintchine_unique", "levy_khintchine_converse", "selfDecomposable_infinitelyDivisible",
 "wolfe_symmetric_unimodal", "schoenberg_radial_bernstein", "karamata_tauberian_zero"]}
outside = {n: [a for a in v if a not in logical and a not in nine] for n, v in report.items()}
outside = {n: v for n, v in outside.items() if v}
print("declarations with an axiom outside the nine+3:", outside)
nonly = sum(1 for v in report.values() if set(v) <= logical)
print("depend on logical only:", nonly, "; depend also on some of the nine:", len(report) - nonly)
used = collections.Counter(a for v in report.values() for a in v if a in nine)
print("usage of the nine:", used)
print("nine never used:", nine - set(used))

# parse inventory from manuscript text, lines 5775..5870
txt = open(base + "/out/A/manuscript.txt", encoding="utf-8", errors="replace").read().split("\n")
block = "\n".join(txt[5774:5872])
block = re.sub(r"\n\s*7[78]\s*\n", "\n", block)
items = re.split(r"\n(?=\s{3,8}(?:Def\.|Lemma|Thm\.|Cor\.|Prop\.) )", "\n" + block)
inventory = collections.OrderedDict()
for it in items:
    it = it.strip()
    if not it:
        continue
    m = re.match(r"((?:Def\.|Lemma|Thm\.|Cor\.|Prop\.) [A0-9.]+), (machine-checked|formalised in Lean): (.*)", it, re.S)
    if not m:
        print("UNPARSED:", it[:60]); continue
    stmt, status, names = m.groups()
    names = re.sub(r"\s+", " ", names.replace("\n", " ")).strip().rstrip(".")
    lst = []
    for n in names.split(","):
        n = n.strip()
        if not n: continue
        n = n.replace(" ", "_")
        lst.append(n)
    inventory[stmt] = (status, lst)
total = sum(len(v[1]) for v in inventory.values())
distinct = set(n for v in inventory.values() for n in v[1])
print("inventory statements:", len(inventory), "names:", total, "distinct:", len(distinct))
dup = collections.Counter(n for v in inventory.values() for n in v[1])
print("names under two statements:", [n for n, c in dup.items() if c > 1])
print("in inventory not in report:", sorted(distinct - set(report)))
print("in report not in inventory:", sorted(set(report) - distinct))
# per statement cited facts
code = {"density_of_integrable_charFun": "C1", "sato_polar_criterion": "C2", "levy_khintchine_exists": "C3(i)",
        "levy_khintchine_unique": "C3(ii)", "levy_khintchine_converse": "C3(iii)",
        "selfDecomposable_infinitelyDivisible": "C4", "wolfe_symmetric_unimodal": "C5",
        "schoenberg_radial_bernstein": "C6", "karamata_tauberian_zero": "C7"}
order = ["C1","C2","C3(i)","C3(ii)","C3(iii)","C4","C5","C6","C7"]
print()
for stmt, (status, lst) in inventory.items():
    facts = set()
    per = {}
    for n in lst:
        if n in report:
            f = [code[a.replace("AffineHemigroup.", "")] for a in report[n] if a in nine]
            per[n] = f
            facts |= set(f)
    fl = [c for c in order if c in facts]
    print(f"{stmt:12s} {status:18s} facts: {fl if fl else 'none'}")
    for n, f in per.items():
        if f:
            print(f"      {n}: {f}")
