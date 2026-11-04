#!/usr/bin/env python3
"""Count typeset lines and vertical extent of a passage of the frozen build.

Usage: typeset_lines.py PDF FIRST_PAGE LAST_PAGE "start phrase" "end phrase"

Reads `pdftotext -bbox-layout` for the pages, clusters words into typeset lines by their
baseline (yMax; a superscript or subscript within 6 pt of a baseline joins it), and reports the
lines from the first line containing the start phrase to the first later line containing the end
phrase, inclusive, with the vertical extent in points (a body line is about 13.55 pt here).
Phrases are matched against the line's words joined by single spaces.
"""
import re
import subprocess
import sys
import xml.etree.ElementTree as ET


def page_lines(pdf, page):
    out = subprocess.run(
        ["pdftotext", "-bbox-layout", "-f", str(page), "-l", str(page), pdf, "-"],
        capture_output=True, text=True, check=True).stdout
    # pdftotext leaves a bare "<" or "&" in a word, so parse the word elements by pattern
    words = []
    for m in re.finditer(r'<word xMin="([0-9.]+)" yMin="[0-9.]+" xMax="[0-9.]+" yMax="([0-9.]+)">(.*?)</word>', out):
        words.append((float(m.group(2)), float(m.group(1)), m.group(3)))
    words.sort()
    lines = []
    for y, x, t in words:
        if lines and abs(y - lines[-1]["y"]) <= 6.0:
            lines[-1]["w"].append((x, t))
        else:
            lines.append({"y": y, "w": [(x, t)]})
    res = []
    for ln in lines:
        ln["w"].sort()
        res.append((page, ln["y"], " ".join(t for _, t in ln["w"])))
    # drop the page number (last line, a bare integer)
    if res and res[-1][2].strip().isdigit():
        res = res[:-1]
    return res


def main():
    pdf, p0, p1, start, end = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
    lines = []
    for p in range(p0, p1 + 1):
        lines.extend(page_lines(pdf, p))
    i0 = next(i for i, l in enumerate(lines) if start in l[2])
    i1 = next(i for i in range(i0, len(lines)) if end in lines[i][2])
    seg = lines[i0:i1 + 1]
    extent = 0.0
    for p in range(p0, p1 + 1):
        ys = [l[1] for l in seg if l[0] == p]
        if ys:
            extent += max(ys) - min(ys) + 13.55
    for p, y, t in seg:
        print(f"p{p} y={y:7.2f} | {t[:110]}")
    print(f"--- {len(seg)} clustered lines, vertical extent {extent:.0f} pt "
          f"= {extent / 13.55:.1f} body-line heights")


if __name__ == "__main__":
    main()
