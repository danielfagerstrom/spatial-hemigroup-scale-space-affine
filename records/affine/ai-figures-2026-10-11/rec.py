# Export note: 1 file path(s) on the author's machine were replaced by <local path> in this public copy; nothing else was changed.
import json,re
rows=[json.loads(l) for l in open('<local path>',encoding='utf-8')]
by={r['id'][:8]:r for r in rows}
runs=[r for r in rows if r['source']=='claude-code' and re.match(r'spatial-hemigroup-affine-q-\d{4}$',r['repo'])]
def A(rs,label):
    act=sum(r['active_s'] for r in rs)/3600; sp=sum(r['duration_s'] for r in rs)/3600
    tw=sum(r['typed_words'] for r in rs); tt=sum(r['typed_turns'] for r in rs); aw=sum(r['assistant_words'] for r in rs)
    dw=sum(r['directed_words'] for r in rs); st=sum(r['subagent_turns'] for r in rs); ns=sum(len(r['subagents']) for r in rs)
    print(f"{label}: n={len(rs)} act={act:.2f} span={sp:.1f} typed={tw}/{tt}t agent={aw} ratio={(aw/tw if tw else float('nan')):.2f} directed={dw} subturns={st} subtraces={ns}")
hub=by['7dbafaad']; lean=by['dd33ba56']
core=runs+[hub]; A(core,'CORE strict')
A(core+[lean],'CORE+Lean')
sh=[by[i] for i in ('89a0f801','46d612ec','47dc0065','a94448d1')]
A(core+sh,'CEIL strict'); A(core+sh+[lean],'CEIL+Lean')
A(runs,'runs only')
print('runs 10-03 and before:',len([r for r in runs if r['started']<'2026-10-04']))
print('subagent traces in hub:',len(hub['subagents']),'in a94:',len(by['a94448d1']['subagents']),'lean:',len(lean['subagents']))
for k in ('89a0f801','46d612ec','47dc0065','a94448d1'): print(k,by[k]['title'],by[k]['started'][:10],by[k]['ended'][:10])
# output tokens
print('hub tokens',hub['tokens'],'lean tokens',lean['tokens'])
# days with sessions in core
days=sorted({r['started'][:10] for r in core+[lean]}|{r['ended'][:10] for r in core+[lean]})
print(len(days),days[:3],days[-3:])
# 
import datetime
d=set()
for r in runs+[hub,lean]:
    a=datetime.date.fromisoformat(r['started'][:10]);b=datetime.date.fromisoformat(r['ended'][:10])
    while a<=b: d.add(a);a+=datetime.timedelta(1)
print('calendar days touched',len(d))
print('days with a start:',len({r['started'][:10] for r in runs+[hub,lean]}))
