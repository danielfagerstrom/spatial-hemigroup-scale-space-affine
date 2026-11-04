import importlib.util,json,re,collections
spec=importlib.util.spec_from_file_location('gen',__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'gen.py')); g=importlib.util.module_from_spec(spec); spec.loader.exec_module(g)
rows=[json.loads(l) for l in open(g.BASE+'sessions.jsonl',encoding='utf-8')]
by={r['id'][:8]:r for r in rows}
turns=g.parse(by['7dbafaad']['path'])
def agents(cut):
    return len({re.search(r'agent (agent-\w+)',h).group(1) for t,h,x in turns if t<=cut and 'agent ' in h})
print('hub agents at 10-03 20:00',agents('2026-10-03 20:00'),'at end',agents('9999'))
hubdays_old={t[:10] for t,h,x in turns if t<='2026-10-03 20:00'}
runs=[r for r in rows if re.match(r'spatial-hemigroup-affine-q-\d{4}$',r['repo'])]
rd_old={r['started'][:10] for r in runs if r['started']<'2026-10-04'}|{r['ended'][:10] for r in runs if r['started']<'2026-10-04'}
print('old days',sorted(hubdays_old|rd_old),len(hubdays_old|rd_old))
newdays=hubdays_old|{t[:10] for t,h,x in turns}|{r['started'][:10] for r in runs}|{r['ended'][:10] for r in runs}
lean=g.parse(by['dd33ba56']['path']); newdays|={t[:10] for t,h,x in lean}
print('new days',len(newdays),sorted(newdays))
# hub typed turns by date for the AI-statement era
c=collections.Counter(t[:10] for t,h,x in turns if h.startswith('human'))
print(sorted(c.items()))
