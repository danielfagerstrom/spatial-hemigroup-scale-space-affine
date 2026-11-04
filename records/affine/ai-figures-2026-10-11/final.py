import importlib.util,json,re,sys
spec=importlib.util.spec_from_file_location('gen',__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'gen.py')); g=importlib.util.module_from_spec(spec); spec.loader.exec_module(g)
rows=[json.loads(l) for l in open(g.BASE+'sessions.jsonl',encoding='utf-8')]
byp={r['id'][:8]:r for r in rows}
def runs(cut):
    return [r for r in rows if r['source']=='claude-code' and re.match(r'spatial-hemigroup-affine-q-\d{4}$',r['repo']) and r['started']<=cut]
def agg(rs):
    return dict(n=len(rs),act=sum(r['active_s'] for r in rs)/3600,span=sum(r['duration_s'] for r in rs)/3600,typed=sum(r['typed_words'] for r in rs),tt=sum(r['typed_turns'] for r in rs),directed=sum(r['directed_words'] for r in rs),aw=sum(r['assistant_words'] for r in rs),subs=sum(len(r['subagents']) for r in rs),subturns=sum(r['subagent_turns'] for r in rs),tok=sum(r['tokens'].get('output',0) for r in rs))
def hubm(id8,cut):
    r=byp[id8]; m=g.metrics(g.parse(r['path']),cut); return m
def total(parts):
    return {k:sum(p[k] for p in parts) for k in parts[0]}
def lean(cut='9999'):
    r=byp['dd33ba56']; return dict(n=1,act=r['active_s']/3600,span=r['duration_s']/3600,typed=r['typed_words'],tt=r['typed_turns'],directed=0,aw=r['assistant_words'],subs=len(r['subagents']),subturns=r['subagent_turns'],tok=r['tokens'].get('output',0))
def H(id8,cut):
    m=hubm(id8,cut); r=byp[id8]
    return dict(n=1 if m['hn'] or m['A'] else 0,act=m['act_h'],span=m['span_h'],typed=m['H'],tt=m['hn'],directed=0,aw=m['A'],subs=0,subturns=0,tok=0)
def show(label,p):
    t=p
    ratio=t['aw']/t['typed'] if t['typed'] else float('nan')
    print(f"{label}: sessions {t['n']}, active {t['act']:.1f} h, span {t['span']:.1f} h, typed {t['typed']} in {t['tt']} turns, agent {t['aw']}, ratio {ratio:.1f}:1, directed(briefs) {t['directed']}")
OLD='2026-10-03T20:00'; NEW='2026-10-10T20:00:30'
c_old=total([agg(runs('2026-10-03T23:59')),H('7dbafaad','2026-10-03 20:00')])
show('CORE old repro (to 10-03 20:00Z)',c_old)
ceil_ids=['89a0f801','46d612ec','47dc0065']
c_oldc=total([c_old]+[H(i,'2026-10-03 20:00') for i in ceil_ids]); show('CEILING old repro',c_oldc)
print()
R=agg(runs('2026-10-10T20:00'));print('runs',R)
h=H('7dbafaad','2026-10-10 20:01')
core_new_nolean=total([R,h]); show('CORE new, strict continuation (queue runs + Paper VII hub session)',core_new_nolean)
core_new=total([R,h,lean()]); show('CORE new + Lean session dd33ba56',core_new)
ceil_new_nolean=total([core_new_nolean]+[H(i,'2026-10-10 20:01') for i in ceil_ids]+[H('a94448d1','2026-10-10 20:01')]); show('CEILING new, strict continuation (+3 old shifts + Overnight shift)',ceil_new_nolean)
ceil_new=total([core_new]+[H(i,'2026-10-10 20:01') for i in ceil_ids]+[H('a94448d1','2026-10-10 20:01')]); show('CEILING new + Lean',ceil_new)
print()
print('Lean',lean()); print('hub',h); print('a94',H('a94448d1','2026-10-10 20:01'))
print('runs list:',sorted(r['branch'] for r in runs('2026-10-10T20:00')))
# range of days
print('first',min(r['started'] for r in runs('9')), 'last archived turn', max(r['ended'] for r in rows if r['source']=='claude-code'))
# per day-cuts for 10-04 check
for cut in ('2026-10-04 23:59',):
    cc=total([agg(runs('2026-10-04T23:59')),H('7dbafaad',cut)]); show('core to 10-04 23:59Z (no Lean)',cc)
