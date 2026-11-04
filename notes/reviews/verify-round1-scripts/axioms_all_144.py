#!/usr/bin/env python3
r"""Round 1 of the external review of iso-review-1, verification of the trust base (item 6b):
Lean's `#print axioms` report for EVERY declaration that Appendix B of the isotropic paper lists
(144 names in 26 rows, 141 of them distinct: three are listed under two statements), and its
comparison with Table 1 of section 1.1. The table is printed, not saved: the record
records/affine/reviews/VERIFY-round1-claims-and-trust-base.md, item 6, holds it.

The referee (review-content-iso-review-1-GPT-6.1-Sol-Ultra.md, section 5): the guard admits
twelve axioms, three of them the companion paper's, the paper claims nine (seven cited facts),
and Appendix B prints the report for eight declarations only.

    python records/affine/reviews/verify-round1-scripts/axioms_all_144.py gen
        writes Formalization/scratch/verify_round1_axioms_all_144.lean (git-ignored): the import
        and one `#print axioms` line per distinct declaration, in the order of Appendix B, and
        prints the command to run.
    (run, ONCE, from Formalization/, one Lean process at a time, on the warm build:)
        lake env lean scratch/verify_round1_axioms_all_144.lean \
          > ../records/affine/reviews/verify-round1-scripts/axioms-all-144-output.txt 2>&1
    python records/affine/reviews/verify-round1-scripts/axioms_all_144.py table
        reads that output; prints the table statement -> axioms (Markdown), and checks
        (a) every declaration was reported, (b) no declaration names an axiom outside Lean's three
        and the nine of this paper, in particular none of the companion paper's three, (c) for
        each statement the union of the axioms of its declarations is the set that Table 1 gives.
        Exit 1 if a check fails.

The list of declarations is not typed here: it is `rows` of records/affine/gen-verification-table.py,
that is, the \lean tags of the blueprint nodes, which `gen-verification-table.py check` compares
with the appendix.
"""
import importlib.util
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN_DIR = ROOT / "Formalization"
SCRATCH = LEAN_DIR / "scratch" / "verify_round1_axioms_all_144.lean"
OUTPUT = HERE / "axioms-all-144-output.txt"

LOGIC = {"propext", "Classical.choice", "Quot.sound"}
NS = "AffineHemigroup."
C = {
    "C1": NS + "density_of_integrable_charFun",
    "C2": NS + "sato_polar_criterion",
    "C3(i)": NS + "levy_khintchine_exists",
    "C3(ii)": NS + "levy_khintchine_unique",
    "C3(iii)": NS + "levy_khintchine_converse",
    "C4": NS + "selfDecomposable_infinitelyDivisible",
    "C5": NS + "wolfe_symmetric_unimodal",
    "C6": NS + "schoenberg_radial_bernstein",
    "C7": NS + "karamata_tauberian_zero",
}
NAME_OF = {v: k for k, v in C.items()}
COMPANION = {NS + "operatorSelfDecomposable_infinitelyDivisible", NS + "khintchine_null_array",
             NS + "gelfand_naimark_logMajorized"}

# Table 1 of section 1.1 (paper-iso/01-introduction.tex, tab:trust-base), row by row: the cited
# facts that the formal proof of each statement rests on. "every other statement: none".
TABLE1 = {
    "thm:isotropic-classification": ["C3(ii)", "C3(iii)"],
    "cor:isotropic-classification-operators": ["C3(ii)", "C3(iii)"],
    "prop:isotropic-polar-reading": ["C2", "C3(i)", "C3(ii)", "C3(iii)", "C4"],
    "thm:origin-boundedness-d": ["C1"],
    "prop:isotropic-radial-monotone": ["C5", "C3(ii)", "C3(iii)", "C2"],
    "prop:origin-lower-bound-d": ["C3(iii)"],
    "prop:origin-upper-bound-d": ["C3(iii)", "C2", "C5"],
    "prop:origin-rate-d": ["C7", "C2", "C3(iii)", "C5"],
    "thm:filtration-strict": ["C2", "C3(i)", "C3(ii)", "C3(iii)", "C4", "C6"],
    "thm:no-cin-ray-in-the-plane": ["C2", "C3(i)", "C3(ii)", "C3(iii)", "C4"],
}
ORDER = ["C1", "C2", "C3(i)", "C3(ii)", "C3(iii)", "C4", "C5", "C6", "C7"]


def generator():
    path = ROOT / "records" / "affine" / "gen-verification-table.py"
    spec = importlib.util.spec_from_file_location("gen_verification_table", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def statements():
    """[(kind, label, [full Lean names])] in the order of Appendix B."""
    g = generator()
    src = g.blueprint()
    out = []
    for kind, label, nodes in g.ROWS:
        names = []
        for node in nodes or [label]:
            for n in g.lean_names(src, node):
                if n not in names:
                    names.append(n)
        out.append((kind, label, names))
    return out


def gen():
    rows = statements()
    total = sum(len(n) for _, _, n in rows)
    distinct = []
    for _, _, names in rows:
        for n in names:
            if n not in distinct:
                distinct.append(n)
    SCRATCH.parent.mkdir(exist_ok=True)
    src = "import AffineHemigroup\n" + "".join(f"#print axioms {n}\n" for n in distinct)
    with open(SCRATCH, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(src)
    print(f"{len(rows)} rows, {total} names, {len(distinct)} distinct")
    print(f"wrote {SCRATCH.relative_to(ROOT)}")
    print("run from Formalization/:  lake env lean scratch/verify_round1_axioms_all_144.lean")


def parse(text):
    """name -> set of axioms, from Lean's output."""
    text = text.replace("\r\n", "\n")
    got = {}
    for m in re.finditer(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.M):
        got[m.group(1)] = {a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()}
    for m in re.finditer(r"^'([^']+)' does not depend on any axioms", text, re.M):
        got[m.group(1)] = set()
    return got


def facts(axioms):
    cited = [k for k in ORDER if C[k] in axioms]
    return ", ".join(cited) if cited else "none"


def table():
    rows = statements()
    got = parse(open(OUTPUT, encoding="utf-8").read())
    ok = True
    lines = []
    problems = []
    lines.append("| statement | declarations | cited facts printed (union) | Table 1 | agrees |")
    lines.append("|---|---:|---|---|---|")
    detail = []
    seen = set()
    for kind, label, names in rows:
        union = set()
        for n in names:
            if n not in got:
                problems.append(f"NOT REPORTED: {n} ({label})")
                ok = False
                continue
            ax = got[n]
            seen.add(n)
            extra = ax - LOGIC - set(C.values())
            if extra:
                problems.append(f"OUTSIDE THE NINE: {n} ({label}): {sorted(extra)}")
                ok = False
            if ax & COMPANION:
                problems.append(f"COMPANION AXIOM: {n} ({label}): {sorted(ax & COMPANION)}")
                ok = False
            union |= ax
            detail.append((label, n, ax))
        want = {C[k] for k in TABLE1.get(label, [])}
        have = union - LOGIC
        agrees = have == want
        if not agrees:
            ok = False
            problems.append(f"TABLE 1 DIFFERS: {label}: Lean {facts(have)}; Table 1 {facts(want)}")
        lines.append(f"| {kind} `{label}` | {len(names)} | {facts(have)} | {facts(want)} | "
                     f"{'yes' if agrees else 'NO'} |")
    lines.append("")
    lines.append("| statement | declaration | logical axioms | cited facts |")
    lines.append("|---|---|---|---|")
    for label, n, ax in detail:
        logic = ", ".join(a for a in ("propext", "Classical.choice", "Quot.sound") if a in ax) or "none"
        lines.append(f"| `{label}` | `{n}` | {logic} | {facts(ax)} |")
    used = set().union(*[ax for _, _, ax in detail]) - LOGIC
    summary = [
        f"rows: {len(rows)}; names: {sum(len(n) for _, _, n in rows)}; distinct: {len(seen)}; "
        f"reported by Lean: {len(got)}",
        "cited facts named by at least one declaration: " + facts(used),
        "cited facts named by none: " + (", ".join(k for k in ORDER if C[k] not in used) or "none"),
        "companion axioms named: " + (", ".join(sorted(used & COMPANION)) or "none"),
        "declarations on no axiom at all: "
        + str(sum(1 for n in seen if not got[n])),
        "declarations on Lean's logical axioms only: "
        + str(sum(1 for n in seen if got[n] and not (got[n] - LOGIC))),
        "declarations naming a cited fact: " + str(sum(1 for n in seen if got[n] - LOGIC)),
    ]
    text = "\n".join(summary) + "\n\n" + "\n".join(lines) + "\n"
    if problems:
        text += "\nPROBLEMS\n" + "\n".join(problems) + "\n"
    print(text)
    print("ALL CHECKS PASS" if ok else "A CHECK FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode == "gen":
        gen()
    elif mode == "table":
        table()
    else:
        sys.exit(__doc__)
