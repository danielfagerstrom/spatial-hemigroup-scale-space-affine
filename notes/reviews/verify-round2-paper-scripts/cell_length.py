#!/usr/bin/env python3
"""Item 4.3: the printed length of Table 2's (similarities, Loewner) cell against the review's
condensed cell, and the symbols each uses.

The current cell is the text pdftotext reads off p. 31 of the frozen build (hyphenation joined);
the proposed cell is the review's text with its LaTeX read as printed glyphs (one character per
symbol). Characters are counted without spaces; the cell's column is 0.27 textwidth, and the
build sets the current cell in 18 lines (p. 31).
"""
import re

CURRENT = (
    "every family's kernels are infinitely divisible with es(ψΣ) ≤ 4 ecc(Σ) (Proposition 4.20(4)); "
    "a uniform bound when the Lévy measures at the thinnest apertures stay comparable to the "
    "isotropic member's, and none in general (Propositions H.5, H.9 and H.6); for a profile bounded "
    "at the origin, shape-blind at the origin (Proposition H.8) and not beyond it (Proposition "
    "H.7(3)); not every family is a Gaussian convolved with a shape-blind part (Proposition H.1(3))"
)

PROPOSED = (
    "every family's kernels are infinitely divisible with anisotropy bounded by es(ψΣ) ≤ 4ecc(Σ) "
    "(Prop. 4.20(4)); non-Gaussian families survive (e.g., µΣ = N(0,2bΣ) ∗ Sα(Σ + κtr(Σ)I), "
    "Prop. H.1(3)); es(ψΣ) is uniformly bounded in Σ when the rank-one limit of LΣ is comparable "
    "to LI, and can grow as a power of ecc(Σ) otherwise (Props. H.5, H.6); when kd(0+) < ∞, LΣ is "
    "asymptotically isotropic at the origin (Prop. H.8) but need not be isotropic away from it "
    "(Prop. H.7)."
)

CURRENT_LINES = 18  # counted on p. 31 of the build


def chars(s):
    return len(re.sub(r"\s", "", s))


def main():
    c, p = chars(CURRENT), chars(PROPOSED)
    per_line = c / CURRENT_LINES
    print(f"current cell : {c} characters, {len(CURRENT.split())} words, {CURRENT_LINES} lines printed")
    print(f"proposed cell: {p} characters, {len(PROPOSED.split())} words, "
          f"about {p / per_line:.1f} lines at the current cell's {per_line:.1f} characters per line")
    print("symbols in the proposed cell that the current cell does not print:")
    for sym in ("N(0,", "Sα(", "κ", "LΣ", "LI", "kd(0+)"):
        print(f"  {sym:8s} current: {'yes' if sym in CURRENT else 'no ':3s}  proposed: "
              f"{'yes' if sym in PROPOSED else 'no'}")
    print("propositions cited:")
    for name, s in (("current", CURRENT), ("proposed", PROPOSED)):
        refs = sorted(set(re.findall(r"(?:4\.20|H\.\d)(?:\(\d\))?", s)))
        print(f"  {name:8s}: {', '.join(refs)}")


if __name__ == "__main__":
    main()
