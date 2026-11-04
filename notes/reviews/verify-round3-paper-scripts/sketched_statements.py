#!/usr/bin/env python3
"""Round-3 verification (report E, finding iii): for each of the twenty statements that the
review-3 build prints with a sketch only (Appendix I, p. 104), find its blueprint node, report its
\\lean tags and \\leanok markers (statement and proof), and measure the blueprint proof of record
against the paper's sketch, in non-comment source characters. Pages are estimated from Appendix C,
which prints proofs of record verbatim (paper/appendix-wedge-axis.tex, pp. 70-83 of the build).
Run from the repository root: python3 records/affine/reviews/verify-round3-paper-scripts/sketched_statements.py
"""
import re, glob, pathlib

ROOT = pathlib.Path('.')
aux = (ROOT / 'paper/main.aux').read_text()
num2labels = {}
for m in re.finditer(r'\\newlabel\{([^}]*)\}\{\{([^}]*)\}\{(\d+)\}', aux):
    lab, num, page = m.group(1), m.group(2), int(m.group(3))
    if lab.startswith(('prop:', 'lem:', 'thm:')):
        num2labels.setdefault(num, []).append((lab, page))

TARGETS = ['4.4', '4.18', '4.24', 'A.3', 'D.1', 'E.1', 'E.4', 'F.2', 'F.3', 'F.4', 'F.5',
           'H.1', 'H.2', 'H.4', 'H.5', 'H.6', 'H.7', 'H.8', '4.14', 'A.5']

def strip_comments(s):
    return '\n'.join(re.sub(r'(?<!\\)%.*', '', l) for l in s.split('\n'))

bp = {}
for f in sorted(glob.glob('blueprint/src/parts/*.tex')):
    bp[f] = pathlib.Path(f).read_text()

paper = {}
for f in sorted(glob.glob('paper/*.tex')):
    paper[f] = pathlib.Path(f).read_text()

def node(label):
    for f, t in bp.items():
        i = t.find('\\label{%s}' % label)
        if i < 0:
            continue
        b = t.rfind('\\begin{', 0, i)
        env = re.match(r'\\begin\{(\w+)\}', t[b:]).group(1)
        e = t.find('\\end{%s}' % env, i)
        stmt = t[b:e]
        p0 = t.find('\\begin{proof}', e)
        nxt = t.find('\\begin{', e + 5)
        # the proof must follow the statement before the next statement environment
        between = t[e:p0]
        if p0 < 0 or re.search(r'\\begin\{(proposition|lemma|theorem|definition|remark)\}', between):
            return f, stmt, None
        p1 = t.find('\\end{proof}', p0)
        return f, stmt, t[p0:p1]
    return None, None, None

def paper_sketch(label):
    # first choice: a proof environment whose optional argument names the label
    for f, t in paper.items():
        m = re.search(r'\\begin\{proof\}(\[[^\]]*\\ref\{%s\}[^\]]*\])' % re.escape(label), t)
        if m:
            p1 = t.find('\\end{proof}', m.start())
            return f, m.group(1), t[m.start():p1]
    # otherwise the first proof after the printed statement
    for f, t in paper.items():
        i = t.find('\\label{%s}' % label)
        if i < 0:
            continue
        m = re.search(r'\\begin\{proof\}(\[[^\]]*\])?', t[i:])
        if not m:
            return f, None, None
        p0 = i + m.start()
        p1 = t.find('\\end{proof}', p0)
        return f, m.group(1), t[p0:p1]
    return None, None, None

# calibration: Appendix C, pp. 70-83 (13.0 pages of mostly proofs of record)
cal = strip_comments(paper['paper/appendix-wedge-axis.tex'])
cal_chars = len(re.sub(r'\s+', ' ', cal))
pages_C = 83 - 70 + 0.0  # D starts on p. 83, C on p. 70: about 13 pages
cpp = cal_chars / pages_C
print(f'calibration: Appendix C {cal_chars} chars over ~{pages_C:.0f} pages = {cpp:.0f} chars/page\n')

tot_bp = tot_sk = 0
print(f"{'no.':5} {'label':42} {'stmt leanok':11} {'proof':6} {'proof leanok':12} {'#lean':5} {'bp proof':>8} {'sketch':>7} {'ratio':>6}")
for n in TARGETS:
    labs = num2labels.get(n, [])
    labs = [l for l in labs if not l[0].endswith(('-statement',))]
    if not labs:
        print(n, 'NOT FOUND'); continue
    lab = labs[0][0]
    f, stmt, proof = node(lab)
    if stmt is None:
        print(n, lab, 'no blueprint node'); continue
    lean = re.search(r'\\lean\{([^}]*)\}', stmt)
    nlean = len([x for x in lean.group(1).split(',') if x.strip()]) if lean else 0
    st_ok = '\\leanok' in stmt
    pr_ok = proof is not None and '\\leanok' in proof
    bpl = len(re.sub(r'\s+', ' ', strip_comments(proof))) if proof else 0
    pf, kind, sk = paper_sketch(lab)
    skl = len(re.sub(r'\s+', ' ', strip_comments(sk))) if sk else 0
    tot_bp += bpl; tot_sk += skl
    ratio = skl / bpl if bpl else float('nan')
    print(f"{n:5} {lab:42} {str(st_ok):11} {str(proof is not None):6} {str(pr_ok):12} {nlean:5} {bpl:8} {skl:7} {ratio:6.2f}  {kind or ''}")
print(f"\ntotal blueprint proofs {tot_bp} chars = {tot_bp/cpp:.1f} pages; sketches {tot_sk} chars = {tot_sk/cpp:.1f} pages;"
      f" net cost of printing all in place of the sketches = {(tot_bp-tot_sk)/cpp:.1f} pages")

# The subset that Table 2 cites in the two smaller-group rows (report E, required change 5).
SUBSET = ['F.2', 'F.3', 'F.4', 'F.5', 'H.1', 'H.2', 'H.4', 'H.5', 'H.6', 'H.7', 'H.8']
sb = ss = 0
for n in SUBSET:
    lab = num2labels[n][0][0]
    _, _, proof = node(lab)
    _, _, sk = paper_sketch(lab)
    sb += len(re.sub(r'\s+', ' ', strip_comments(proof)))
    ss += len(re.sub(r'\s+', ' ', strip_comments(sk)))
print(f"subset {', '.join(SUBSET)}: blueprint proofs {sb/cpp:.1f} pages, sketches {ss/cpp:.1f} pages, net {(sb-ss)/cpp:.1f} pages")
