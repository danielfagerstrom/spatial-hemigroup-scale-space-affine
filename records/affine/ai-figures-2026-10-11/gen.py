# Export note: 1 file path(s) on the author's machine were replaced by <local path> in this public copy; nothing else was changed.
import re,sys,json,itertools
from datetime import datetime
BASE='<local path>'
tool=re.compile(r'^`[^`]+` — ')
def prose(t): return '\n'.join(l for l in t.split('\n') if not tool.match(l.strip()))
def parse(path):
    txt=open(BASE+path,encoding='utf-8').read()
    m=re.search(r'\n# [^\n]*\n',txt); body=txt[m.end()-1:]
    parts=re.split(r'\n## (\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) — ([^\n]*)\n','\n'+body)
    return [(parts[i],parts[i+1],parts[i+2]) for i in range(1,len(parts),3)]
def metrics(turns,cut='9999',since='0000'):
    ts=[];H=hn=A=0
    for t,h,x in turns:
        if t>cut or t<since: continue
        ts.append(datetime.fromisoformat(t))
        if h.startswith('human'): H+=len(x.split());hn+=1
        elif h.startswith('assistant'): A+=len(prose(x).split())
    ts.sort()
    gaps=[(b-a).total_seconds() for a,b in zip(ts,ts[1:])]
    act=sum(min(g,900) for g in gaps)-0.5*sum(1 for g in gaps if g<900)  # correct for second-truncated headings (model floors each gap on ms timestamps)
    span=(ts[-1]-ts[0]).total_seconds() if ts else 0
    return dict(hn=hn,H=H,A=A,act_h=act/3600,span_h=span/3600,start=str(ts[0]) if ts else None,end=str(ts[-1]) if ts else None)
if __name__=='__main__':
    rows=[json.loads(l) for l in open(BASE+'sessions.jsonl',encoding='utf-8')]
    byid={r['id']:r for r in rows}
    path=byid[sys.argv[1]]['path']; cut=sys.argv[2] if len(sys.argv)>2 else '9999'
    r=byid[sys.argv[1]]
    print(r['title'],'recorded: act',r['active_s']/3600,'span',r['duration_s']/3600)
    print(metrics(parse(path),cut))
