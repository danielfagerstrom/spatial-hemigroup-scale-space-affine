#!/usr/bin/env python3
"""Item 10: the printed size of the labels of Figures 1-3 in the frozen build.

Printed size = font size in the script x (printed width / figure width). The figure width is the
script's figsize (savefig without bbox_inches="tight", so the PNG is figsize x dpi); the printed
width is the PNG's pixel width over the x-ppi at which `pdfimages -list` reports it placed in the
PDF. The font sizes are read off the scripts (file:line in the table below); matplotlib's
defaults are font.size 10 and "medium" (= font.size) for axis labels, tick labels and legends.
Run from the repository root.
"""
import re
import subprocess

PDF = "paper/main.pdf"

# figure, page, script, figsize width (in), [(label, font size, where)]
FIGS = [
    ("Figure 1 (fig-rank-deficient-step)", 21, 4.6, [
        ("legend (Sigma = I, Sigma + P, range of P, <x,w> = +-1)", 8, "fig-rank-deficient-step.py:82"),
        ("the letter w", 10, "fig-rank-deficient-step.py:74"),
    ]),
    ("Figure 2 (fig-shape-plane)", 29, 6.3, [
        ("every label: titles, axis labels, ticks, alpha =, rays, Loewner", 8,
         "fig-shape-plane.py:131 (rcParams font.size 8), :167, :191"),
    ]),
    ("Figure 3 (fig-cones-plane)", 33, 8.2, [
        ("panel titles, axis labels (u, change of shape; a, growth in size; u; v)", 10,
         "fig-cones-plane.py:108-110, 131-133 (default 10)"),
        ("legend (C1, k = 1/3 ...), annotations (non-Gaussian families ...)", 8,
         "fig-cones-plane.py:124-128, 139"),
        ("the word rays in (b)", 7.5, "fig-cones-plane.py:122"),
    ]),
]


def placements():
    out = subprocess.run(["pdfimages", "-list", PDF], capture_output=True, text=True, check=True).stdout
    res = {}
    for line in out.splitlines()[2:]:
        f = line.split()
        if f[2] == "image":
            res[int(f[0])] = (int(f[3]), float(f[12]))  # width px, x-ppi
    return res


def main():
    pl = placements()
    print("body text 11 pt; \\scriptsize 8 pt, \\footnotesize 9 pt in the 11 pt article class\n")
    for name, page, fig_w, labels in FIGS:
        px, ppi = pl[page]
        printed = px / ppi
        scale = printed / fig_w
        print(f"{name}, p. {page}: {px} px at {ppi:.0f} ppi = {printed:.2f} in printed; "
              f"figsize width {fig_w} in; scale {scale:.3f}")
        for lab, fs, where in labels:
            need9 = 9 / scale
            print(f"  {fs:4.1f} pt in script -> {fs * scale:4.1f} pt printed   {lab}   [{where}]"
                  f"   (9 pt printed needs {need9:.1f} pt in the script)")
        print()


if __name__ == "__main__":
    main()
