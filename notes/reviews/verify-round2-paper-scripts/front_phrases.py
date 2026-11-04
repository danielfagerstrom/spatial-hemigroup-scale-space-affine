"""Locate phrases of the round-2 presentation review (items 1-3, 16-18) in the frozen build.

Usage: python3 front_phrases.py <pdftotext -layout output of review-build-review-2.pdf>
Pages are split on form feeds; whitespace (and hyphenation at line ends) is normalized,
so a phrase broken over lines is found. Printed page = PDF page for this build (p. 1 prints 1).
"""
import re
import sys

pages = open(sys.argv[1], encoding="utf-8").read().split("\f")
norm = [re.sub(r"\s+", " ", re.sub(r"-\n\s*", "", p)) for p in pages]

PHRASES = [
    "Working draft",
    "not yet released",
    "a further paper",
    "released version 0.1",
    "the line paper",
    "the cone paper",
    "the isotropic paper",
    "line paper",
    "cone paper",
    "isotropic paper",
    "notes/PROCESS.md",
    "computed 2026-10-13",
    "Sketch",
    "Twenty statements have a sketch only",
    "rest on no cited fact",
    "Lean's three logical axioms",
    "Lean’s three logical axioms",
    "Where positivity enters is Remark 3.11",
    "sets the axiomatics side by side",
    "Remark 3.13 shows how",
    "incomparable with the classical ones",
    "covariance matrices",
    "its transform for short",
    "keep their meaning",
    "re-measurement of the image, which the iteration makes in any case",
]
for ph in PHRASES:
    hits = [(i + 1, n.count(ph)) for i, n in enumerate(norm) if ph in n]
    total = sum(c for _, c in hits)
    print(f"{ph!r}: {total} occurrence(s) on pages {[p for p, _ in hits]}")
