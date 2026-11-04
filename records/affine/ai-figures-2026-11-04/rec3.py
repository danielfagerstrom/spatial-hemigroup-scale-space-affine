# Export note: 1 file path(s) on the author's machine were replaced by <local path> in this public copy; nothing else was changed.
# rec3.py -- re-derivation for pass 5 of the affine paper, computed 2026-11-04 (archive synced through 2026-11-04 20:33:13 UTC).
# Read-only over ai-archive/canonical. Prints counts and timestamps only, never transcript text.
# Run: PYTHONIOENCODING=utf-8 python rec3.py > rec3-output.txt
import json,re,datetime as dt
ROOT='<local path>'
CUT='2026-11-04 20:33:13'          # one cut for everything (UTC): the archive last turn; session 33b1ecdc is counted to it.
ISO_RELEASE='2026-10-14 05:27:52'  # tag iso-v0.1 (UTC), for the window figures
HEAD=re.compile(r'^## (\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) — (.*)$',re.M)
TOOL=re.compile(r'^`[^`\n]+` — .*$',re.M)
PASTE=re.compile(r'<pasted_content id="[^"]*">(.*?)(?:</pasted_content[^>]*>|\Z)',re.S)
rows=[json.loads(l) for l in open(ROOT+'sessions.jsonl',encoding='utf-8')]
by={r['id'][:8]:r for r in rows}
EXCL={
 ('7dbafaad','2026-10-12 07:44:22'):5454,  # (a) referee report A by another AI system (GPT-6.1 Sol Ultra), whole turn
 ('7dbafaad','2026-10-12 07:45:24'):2145,  # (a) referee report B, whole turn
 ('057cfca0','2026-11-03 18:02:04'):7043,  # (a) report headed Gemini 4 Argon High; the 4-word label line (7047-7043) is kept as the author
 ('0cad1fd5','2026-10-24 08:49:11'):161,   # (b) terminal session text (shell prompt and output), whole turn
 ('0cad1fd5','2026-10-24 10:38:22'):172,   # (b) terminal session text, whole turn
 ('0cad1fd5','2026-10-24 13:39:34'):278,   # (b) terminal session text, whole turn
}
def turns(r):
    t=open(ROOT+r['path'],encoding='utf-8').read(); ms=list(HEAD.finditer(t)); out=[]
    for i,m in enumerate(ms):
        who=m.group(2); body=t[m.end():ms[i+1].start() if i+1<len(ms) else len(t)].strip()
        k='typed' if who=='human' else 'directed' if who.startswith('human') else 'asst' if who.startswith('assistant') else 'other'
        w=len((TOOL.sub('',body) if k=='asst' else body).split())
        out.append((m.group(1),k,w,body,who))
    return [x for x in out if x[0]!='unknown']
def secs(a,b): return int((dt.datetime.fromisoformat(b)-dt.datetime.fromisoformat(a)).total_seconds())
def active(ts): return sum(min(secs(a,b),900) for a,b in zip(ts,ts[1:]))
def stats(sel,lo=None,exclude=None,pasted=False):
    # Whole-session figures come from the archive row; with lo (a window) from parsed turns, active time scaled to the archive value.
    # exclude: dict as EXCL. pasted=True also removes every pasted_content block from typed words (sensitivity only).
    exclude=exclude or {}
    S=dict(n=0,tw=0,tt=0,aw=0,act=0.0,span=0,sub=0,ts=[])
    for r in sel:
        T=turns(r); assert all(x[0]<=CUT for x in T),r['id']
        U=[x for x in T if lo is None or x[0]>=lo]
        if not U: continue
        ts=sorted(x[0] for x in U); S['n']+=1; S['ts']+=ts
        if lo is None:
            assert sum(w for _,k,w,_,_ in T if k=='typed')==r['typed_words'],r['id']
            S['aw']+=r['assistant_words']; S['act']+=r['active_s']; S['span']+=r['duration_s']; S['sub']+=len(r['subagents'])
        else:
            S['aw']+=sum(w for _,k,w,_,_ in U if k=='asst')
            S['act']+=active(ts)*r['active_s']/max(1,active(sorted(x[0] for x in T)))
            S['span']+=secs(ts[0],ts[-1])
            S['sub']+=len({a for a in re.findall(r'agent (agent-\w+)',' '.join(x[4] for x in U))})
        for t,k,w,b,who in U:
            if k!='typed': continue
            ex=exclude.get((r['id'][:8],t),0); assert ex<=w
            if pasted and not ex: ex=sum(len(p.split()) for p in PASTE.findall(b))
            if w-ex>0: S['tw']+=w-ex; S['tt']+=1
    return S
def show(label,S):
    ts=S['ts']; wall=secs(min(ts),max(ts))/3600
    print(f"{label}: sessions={S['n']} subagent_traces={S['sub']} first={min(ts)} last={max(ts)} UTC days={len({t[:10] for t in ts})} wall={wall:.0f}h\n"
          f"     typed={S['tw']}w/{S['tt']}t agents={S['aw']} ratio={S['aw']/S['tw']:.1f} active={S['act']/3600:.1f}h span_sum={S['span']/3600:.1f}h")
CC=lambda r:r['source']=='claude-code'
tagged=[r for r in rows if CC(r) and r['repo'].startswith('spatial-hemigroup-affine-')]
hub,lean=by['7dbafaad'],by['dd33ba56']
named=[r for r in rows if CC(r) and re.search('affine',r['title']+' '+r['branch'],re.I) and not r['repo'].startswith('spatial-hemigroup-affine') and r['id'][:8] not in ('7dbafaad','a94448d1')]
ADD=[by[i] for i in ('057cfca0','25478c56','0cad1fd5','33b1ecdc')]
def uniq(L):
    seen=set(); o=[]
    for r in L:
        if r['id'] not in seen: seen.add(r['id']); o.append(r)
    return o
CORE=uniq(tagged+[hub,lean]+named+ADD)
SHIFT=[by[i] for i in ('89a0f801','46d612ec','47dc0065','a94448d1')]
CEIL=uniq(CORE+SHIFT)
NOLEAN=lambda L:[r for r in L if r is not lean]
if __name__=='__main__':
    print('computed 2026-11-04; archive last turn (any session):',max(r['ended'] for r in rows),'| cut used (UTC):',CUT)
    print('core',len(CORE),'ceiling',len(CEIL),'| tagged',len(tagged),'(q',sum('-q-' in r['repo'] for r in tagged),'eval',sum('-eval-' in r['repo'] for r in tagged),'review',sum('-review-' in r['repo'] for r in tagged),') named',[r['id'][:8] for r in named],'added',[r['id'][:8] for r in ADD])
    print('exclusions (session, ts, words):')
    for k,v in EXCL.items(): print('  ',k[0],k[1],v)
    print('  total',sum(EXCL.values()),'in',len(EXCL),'turns')
    for lab,sel in (('CORE',CORE),('CEILING',CEIL)):
        print('\n##',lab)
        show('  raw',stats(sel)); show('  with exclusions',stats(sel,exclude=EXCL))
        show('  with exclusions, without Lean session',stats(NOLEAN(sel),exclude=EXCL))
        show('  sensitivity: exclusions + every pasted_content block',stats(sel,exclude=EXCL,pasted=True))
        AI_ONLY={k:v for k,v in EXCL.items() if k[0]!='0cad1fd5'}  # only AI reports out, all terminal text kept: added by the session
        show('  AI reports out, all terminal text kept',stats(sel,exclude=AI_ONLY))
    for lab,sel in (('CORE',CORE),('CEILING',CEIL)):
        print('\n## window from iso-v0.1 (turns >=',ISO_RELEASE,') --',lab)
        show('  with exclusions',stats(sel,lo=ISO_RELEASE,exclude=EXCL))
    print('\n## typed turns >=100 words in the four added sessions (ts, words, excluded words)')
    for r in ADD:
        for t,k,w,b,who in turns(r):
            if k=='typed' and w>=100: print('  ',r['id'][:8],t,w,EXCL.get((r['id'][:8],t),0))
    print('\n## Agent tool calls and recorded subagent traces in the added sessions')
    for r in ADD: print('  ',r['id'][:8],'Agent calls',r['tools'].get('Agent',0),'traces',len(r['subagents']),'subagent_turns',r['subagent_turns'],'active_h',round(r['active_s']/3600,1))
