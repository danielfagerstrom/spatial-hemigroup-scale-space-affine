"""For each statement Appendix I lists as having "a sketch only", report the heading of the
paper's proof, its length in words, and the length of the blueprint's proof of the same node.

Usage: python3 sketch_headings.py <repo root>
Read-only. A paper proof is the proof environment whose heading \\refs the label (a deferred proof), else
the one under a "% proof of <label>" marker, else the first after the statement's \\label. A blueprint proof is the first
proof environment after the node's \\label in blueprint/src/parts/*.tex.
"""
import glob
import re
import sys

root = sys.argv[1]
LABELS = [
    "prop:affine-orbits", "prop:rational-symbols", "prop:similarity-stable-order-families",
    "prop:isotropic-corner", "prop:glplus-families", "prop:tempered-step-cone",
    "prop:matern-negative-mass", "prop:fixed-frame-families", "prop:similarity-ray-families",
    "prop:diagonal-ray-families", "prop:diagonal-stable-order-families",
    "prop:similarity-stable-family", "prop:similarity-orbit-family",
    "prop:similarity-general-sandwich", "prop:similarity-general-bounded-shape",
    "prop:similarity-degenerate-family", "prop:similarity-line-family",
    "prop:similarity-general-index-zero", "lem:dilation-ratio", "lem:parameter-space",
]
# printed numbers from main.aux
aux = open(f"{root}/paper/main.aux", encoding="utf-8").read()
num = dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^}]*)\}", aux))

def texts(pattern):
    out = {}
    for f in sorted(glob.glob(pattern)):
        out[f] = open(f, encoding="utf-8").read()
    return out

paper = texts(f"{root}/paper/*.tex")
bp = texts(f"{root}/blueprint/src/parts/*.tex")
PROOF = re.compile(r"\\begin\{proof\}(\[[^\]]*\])?(.*?)\\end\{proof\}", re.S)

def words(s):
    s = re.sub(r"(?m)^\s*%.*$", "", s)
    return len(s.split())

def find_after(files, label, marker=False):
    if marker:
        for f, t in files.items():
            for p in PROOF.finditer(t):
                if p.group(1) and ("\\ref{" + label + "}") in p.group(1):
                    return f, p
    for f, t in files.items():
        if marker:
            m = re.search(r"% proof of " + re.escape(label) + r"\s*\n", t)
            if m:
                p = PROOF.search(t, m.end())
                if p:
                    return f, p
        i = t.find("\\label{" + label + "}")
        if i >= 0:
            p = PROOF.search(t, i)
            return f, p
    return None, None

for lab in LABELS:
    pf, pp = find_after(paper, lab, marker=True)
    bf, bpp = find_after(bp, lab)
    head = (pp.group(1) or "[Proof]") if pp else "-"
    pw = words(pp.group(2)) if pp else 0
    bw = words(bpp.group(2)) if bpp else 0
    print(f"{num.get(lab, '?'):6} {lab:42} paper {head:10} {pw:5} words ({pf.split('/')[-1] if pf else '-'}); "
          f"blueprint {bw:5} words ({bf.split('/')[-1] if bf else '-'})")
