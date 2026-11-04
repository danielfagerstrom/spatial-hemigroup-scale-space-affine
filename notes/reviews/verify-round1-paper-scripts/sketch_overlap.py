"""Round-1 verification (Gemini report, section 7.3): how much of each body sketch repeats its full proof.

For the three statements the report names (Lemma 4.8 = lem:stable-tail, Proposition 4.13 =
prop:orbit-step-cone, Theorem 4.21 = thm:wedge-axis) this reads the body's sketch and Appendix C's
complete proof from the paper sources, strips comments and LaTeX commands to words, and reports:

  - the length of each in words;
  - the share of the sketch's word 4-grams that also occur in the full proof (verbatim reuse);
  - difflib's matching-block share of the sketch (a word-sequence alignment).

A high 4-gram share means the sketch copies sentences of the full proof; a low one with similar
content means it summarizes them. Run from the repository root:
    python3 -I records/affine/reviews/verify-round1-paper-scripts/sketch_overlap.py
"""
import difflib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BS = chr(92)

PAIRS = [
    ("Lemma 4.8 (lem:stable-tail)", "paper/05-orbits.tex", 283, 298,
     "paper/appendix-wedge-axis.tex", 514, 570),
    ("Proposition 4.13 (prop:orbit-step-cone)", "paper/05-orbits.tex", 564, 585,
     "paper/appendix-wedge-axis.tex", 572, 623),
    ("Theorem 4.21 (thm:wedge-axis)", "paper/05-wedge-axis.tex", 102, 163,
     "paper/appendix-wedge-axis.tex", 775, 926),
]


def lines(path, a, b):
    text = (ROOT / path).read_text(encoding="utf-8").splitlines()[a - 1:b]
    return "\n".join(l.split("%")[0] if not l.lstrip().startswith("%") else "" for l in text)


def words(tex):
    t = re.sub(re.escape(BS) + r"[A-Za-z]+", " ", tex)
    t = re.sub(r"[^A-Za-z0-9]+", " ", t)
    return [w.lower() for w in t.split() if len(w) > 1 or w.isalpha()]


def grams(ws, n=4):
    return [tuple(ws[i:i + n]) for i in range(len(ws) - n + 1)]


def main():
    print(f"{'statement':42} {'sketch words':>12} {'full words':>10} {'4-gram share':>12} {'aligned share':>13}")
    for name, sf, sa, sb, ff, fa, fb in PAIRS:
        s, f = words(lines(sf, sa, sb)), words(lines(ff, fa, fb))
        gs, gf = grams(s), set(grams(f))
        share = sum(g in gf for g in gs) / max(1, len(gs))
        sm = difflib.SequenceMatcher(None, s, f, autojunk=False)
        aligned = sum(m.size for m in sm.get_matching_blocks()) / max(1, len(s))
        print(f"{name:42} {len(s):12d} {len(f):10d} {share:12.2f} {aligned:13.2f}")


if __name__ == "__main__":
    main()
