"""Locate the phrases quoted by the round-3 content reviews A (sections 1-2) and B (section 3,
Appendix A) in the frozen build review-build-review-3.pdf.

Usage: python3 front_classical_phrases.py <pdftotext -layout output of review-build-review-3.pdf>
Pages are split on form feeds; whitespace (and hyphenation at line ends) is normalized, so a
phrase broken over lines is found. Printed page = PDF page for this build (p. 1 prints 1).
A phrase with mathematics is searched by a plain-text fragment of it.
"""
import re
import sys

pages = open(sys.argv[1], encoding="utf-8").read().split("\f")
norm = [re.sub(r"\s+", " ", re.sub(r"-\n\s*", "", p)) for p in pages]

PHRASES = [
    # report A
    ("A", "completely in some cases, by bounds or examples in others"),
    ("A", "The main result of the paper is the classification"),
    ("A", "a complete description in some cases"),
    ("A", "Shape-adapted apertures are such steps from the first stage"),
    ("A", "Every other such kernel measures the image afresh there"),
    ("A", "loses only the cascade between the stages of the iteration"),
    ("A", "as far as the apertures are concerned"),
    ("A", "how the selection and its iteration behave for the non-Gaussian orbits is not treated"),
    ("A", "Off W a change of aperture is a re-measurement of the original image"),
    ("A", "Table 3 gives the limit kernel by kernel"),
    ("A", "keeps every rotation-invariant one in every column, the Loewner column included"),
    ("A", "used through the six statements restated in"),
    ("A", "four cells of Table 2 stop short of a classification"),
    ("A", "Every definition, lemma, proposition and theorem of"),
    ("A", "So is every proposition and lemma their proofs spend"),
    ("A", "are proved in its released version"),
    ("A", "no formal development of the line paper"),
    ("A", "His scale is a positive definite 2 × 2 matrix"),
    ("A", "this is their sentence applied to a family completed around that measure"),
    ("A", "eqs. (24)–(30), p. 10"),
    ("A", "The results are machine-checked in Lean 4"),
    ("A", "The frequency has three letters"),
    ("A", "Through the singular matrix I"),
    ("A", "which carry the name of the Matérn covariances"),
    ("A", "it overestimates the anisotropy"),
    ("A", "The order appears in his later work as the meaning of a larger matrix scale"),
    ("A", "gelfand naimark logMajorized"),
    # report B
    ("B", "The base must be positive definite"),
    ("B", "the last clause of the definition lists them as the corners"),
    ("B", "It adds continuity in the pair"),
    ("B", "and so is every kernel from scale zero"),
    ("B", "With the ray chains from 0, which every order"),
    ("B", "Asking it at every pair would exclude a family"),
    ("B", "the line’s Lemma 2.2 proved again in Rd with balls for intervals"),
    ("B", "machine-checked on Lean’s logical axioms alone"),
    ("B", "A sketched statement is machine-checked like every other"),
    ("B", "once their transforms have no zeros"),
    ("B", "If no µ"),
    ("B", "so the kernels from scale zero of a cascade family are self-decomposable for every wedge datum"),
    ("B", "The pair (G, W ) is called a wedge datum after its order"),
    ("B", "although Definition 3.1 does not require one"),
    ("B", "Drawn by a script deposited with the paper"),
    ("B", "So the first coordinate of µI is independent of the others"),
    ("B", "With the similarities, non-Gaussian families cascade along the Loewner order"),
    ("B", "That the relation of Kα is one is Proposition 4.7(2), proved without this theorem"),
]
for who, ph in PHRASES:
    key = re.sub(r"\s+", " ", ph)
    hits = [i + 1 for i, p in enumerate(norm) if key in p]
    print(f"[{who}] {ph!r}: pages {hits if hits else 'NOT FOUND'}")
