#!/usr/bin/env python3
"""Independent full-envelope parser and directed oracle for O2a scratch campaign."""
import argparse
from pathlib import Path

def need(ok, why):
    if not ok: raise RuntimeError(why)

def parse(path):
    lines=iter(path.read_text().splitlines())
    def get():
        try: return next(lines)
        except StopIteration: raise RuntimeError('truncated envelope')
    def num(): return int(get())
    out=[]
    while True:
        try: name=next(lines)
        except StopIteration: break
        need(get()=='BEGIN_O2a_ENVELOPE',f'{name}: begin')
        status,phase,tag,reason,fi,fo,steps,pc,fp=(num() for _ in range(9))
        ck=get()
        if ck=='CHECKER': checker=(num(),num(),num())
        else:
            need(ck=='NO_CHECKER',f'{name}: checker marker')
            checker=None
        size=num()
        runs=[]
        while True:
            marker=get()
            if marker=='END_CELLS': break
            need(marker=='RUN',f'{name}: run marker')
            start,count=num(),num()
            kind=get()
            if kind=='UNKNOWN': value=None
            else:
                need(kind=='FIXED',f'{name}: cell kind')
                value=num()
            origin,image=num(),num()
            need(start==sum(x[1] for x in runs),f'{name}: run alignment')
            need(count>0 and start+count<=size,f'{name}: run bounds')
            need(image==(0 if value is None else value),f'{name}: image mismatch')
            need(0<=origin<=8,f'{name}: origin range')
            need(not runs or runs[-1][2:]!=(value,origin,image),f'{name}: duplicate runs')
            runs.append((start,count,value,origin,image))
        need(sum(x[1] for x in runs)==size,f'{name}: size')
        pairs=[]
        while True:
            marker=get()
            if marker=='END_PAIRS': break
            pairs.append((int(marker),num()))
        events=[]
        while True:
            marker=get()
            if marker=='END_EVENTS': break
            events.append(tuple([int(marker)]+[num() for _ in range(13)]))
        need(get()=='END_O2a_ENVELOPE',f'{name}: end')
        need(size==65536,f'{name}: memory size')
        need(0<=status<=16 and 0<=phase<=10 and 0<=tag<=3 and 0<=reason<=2,f'{name}: header range')
        need(all(0<=a<size and 0<=b<size for a,b in pairs),f'{name}: pairs bounds')
        need(all(0<=e[0]<=12 and 0<=e[1]<=6 and 0<=e[2]<=10 and 0<=e[11]<=8 and e[12] in (0,1) and 0<=e[13]<=16 and e[3]<=steps for e in events),f'{name}: event range')
        need((checker is None)==(tag==0 or status==16),f'{name}: checker/tag consistency')
        if tag in (2,3):
            need(checker==(pc,fp,5 if tag==2 else 1),f'{name}: checker state/verdict')
        out.append(dict(name=name,status=status,phase=phase,tag=tag,reason=reason,fi=fi,fo=fo,steps=steps,pc=pc,fp=fp,checker=checker,size=size,runs=runs,pairs=pairs,events=events))
    return out

def cell(case,index):
    for start,count,value,origin,image in case['runs']:
        if start<=index<start+count: return (value,origin,image)
    raise RuntimeError(f"{case['name']}: missing cell {index}")

def summary(case):
    ks=(0,2,4,5,7,8,9,10,12)
    return {'name':case['name'],'header':tuple(case[k] for k in ('status','phase','tag','fi','fo','steps','pc','fp','checker')),
            'cells':{i:cell(case,i) for i in (0,1,2,3,4,5,6,7)},'pairs':case['pairs'],
            'events':[(e[0],e[1],e[2],e[3],e[7],e[8],e[9],e[11],e[12],e[13]) for e in case['events']]}

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('c'); ap.add_argument('lean'); ap.add_argument('--dump',action='store_true'); a=ap.parse_args()
    c=Path(a.c); l=Path(a.lean)
    need(c.read_bytes()==l.read_bytes(),'C/Lean complete output mismatch')
    cases=parse(c)
    names=['ONE_KNOWN','CHAIN','CHAIN_REVERSED','DEFAULT','LATE_SET','EAGER_ZERO','FIXED_CONFLICT','REPEATED','POINTER_ALIAS','ADDRESS_PRIORITY','PUBLIC_PRIORITY','TERMINAL_FRAME']
    need([x['name'] for x in cases]==names,'case sequence')
    oracle={
      'ONE_KNOWN': ((1,0,3,0,0,0,1,2,1,(2,1,1)),[(3,4)],{2:(2,4,2),3:(9,7,9),4:(9,4,9)}),
      'CHAIN': ((2,0,2,0,0,0,2,4,1,(4,1,5)),[(3,4),(4,5)],{3:(9,7,9),4:(9,7,9),5:(9,4,9)}),
      'CHAIN_REVERSED': ((2,0,2,0,0,0,2,4,1,(4,1,5)),[(4,5),(3,4)],{3:(9,7,9),4:(9,7,9),5:(9,4,9)}),
      'DEFAULT': ((2,0,2,0,0,0,2,4,1,(4,1,5)),[(3,4),(4,5)],{3:(0,8,0),4:(0,8,0),5:(0,8,0)}),
      'LATE_SET': ((1,0,3,0,0,0,3,8,1,(8,1,1)),[(3,4)],{3:(9,7,9),4:(9,6,9),6:(0,5,0),7:(9,6,9)}),
      'EAGER_ZERO': ((8,8,0,0,4,0,2,4,1,None),[(3,4)],{3:(0,5,0),4:(0,7,0),6:(0,5,0),7:(0,6,0)}),
      'FIXED_CONFLICT': ((16,9,0,0,3,5,1,2,1,None),[(3,4),(4,5)],{3:(5,4,5),4:(5,7,5),5:(9,4,9)}),
      'REPEATED': ((2,0,2,0,0,0,2,4,1,(4,1,5)),[(3,4),(3,4)],{3:(9,7,9),4:(9,4,9)}),
      'POINTER_ALIAS': ((1,0,3,0,0,0,1,2,1,(2,1,1)),[(2,3)],{2:(1,4,1),3:(1,4,1)}),
      'ADDRESS_PRIORITY': ((7,5,0,0,0,0,0,1,1,None),[],{2:(1<<128,4,1<<128),3:(None,0,0),4:(None,0,0)}),
      'PUBLIC_PRIORITY': ((4,0,0,0,0,0,0,1,1,None),[],{0:(1,1,1),1:(None,0,0),2:(None,0,0)}),
      'TERMINAL_FRAME': ((12,2,1,0,0,0,2,8,2,(8,2,3)),[(3,4)],{3:(9,7,9),4:(9,4,9),5:(1,4,1),6:(8,4,8),7:(2,4,2)})
    }
    byname={x['name']:x for x in cases}
    for name,(header,pairs,cells) in oracle.items():
        x=byname[name]
        got=tuple(x[k] for k in ('status','phase','tag','reason','fi','fo','steps','pc','fp','checker'))
        need(got==header,f'{name}: directed header {got} != {header}')
        need(x['pairs']==pairs,f'{name}: pending order')
        for i,expected in cells.items(): need(cell(x,i)==expected,f'{name}: cell {i}')
        need(all(cell(x,u)[2]==cell(x,v)[2] for u,v in pairs) if x['tag'] in (1,2,3) else True,f'{name}: pair image')
    def events(name,kind): return [e for e in byname[name]['events'] if e[0]==kind]
    need([(e[7],e[9],e[11],e[3]) for e in events('ONE_KNOWN',12)]==[(3,9,7,0)],'one known propagation event')
    need([(e[7],e[3]) for e in events('CHAIN',12)]==[(3,1),(4,1)],'chain propagation chronology')
    need([(e[7],e[3]) for e in events('CHAIN_REVERSED',12)]==[(4,0),(3,1)],'reverse propagation chronology')
    need([(e[7],e[9],e[11],e[3],e[1],e[2]) for e in events('DEFAULT',12)]==[(3,0,8,2,4,9),(4,0,8,2,4,9),(5,0,8,2,4,9)],'terminal default event provenance')
    late=byname['LATE_SET']['events']
    need([(e[0],e[1],e[3],e[7],e[9]) for e in late if e[0] in (7,12) and e[7] in (3,4,7)]==[(7,3,1,4,9),(12,3,1,3,9),(7,1,2,7,9)],'late assignment, propagation, observation order')
    early=byname['EAGER_ZERO']['events']
    need([(e[0],e[7],e[11]) for e in early if e[0] in (5,12) and e[7] in (3,4)]==[(5,3,5),(12,4,7)],'eager zero propagation order')
    need(early[-2][0]==7 and early[-2][7]==4 and early[-2][12]==0 and early[-2][13]==8 and early[-1][0]==10 and early[-1][13]==8,'eager zero assignment conflict trace')
    conflict=byname['FIXED_CONFLICT']['events']
    need(conflict[-2][0]==8 and conflict[-2][7:9]==(4,5) and conflict[-1][0]==10 and conflict[-1][7:9]==(3,5) and conflict[-1][13]==16,'transitive conflict witness and pending chronology')
    need([e[7] for e in events('ADDRESS_PRIORITY',4)]==[0] and not events('ADDRESS_PRIORITY',8),'address failure precedes pending insertion')
    need([e[0] for e in byname['PUBLIC_PRIORITY']['events']]==[11,0,10],'public conflict precedes advice and fuel')
    terminal=byname['TERMINAL_FRAME']
    need(terminal['events'][-1][0]==10 and terminal['events'][-1][2]==2 and terminal['events'][-1][13]==12 and not events('TERMINAL_FRAME',12)[1:],'terminal frame after settled pair')
    need([cell(byname['CHAIN'],i) for i in range(65536)]==[cell(byname['CHAIN_REVERSED'],i) for i in range(65536)],'chain image/order independence')
    if a.dump:
        import json
        for x in cases: print(json.dumps(summary(x)))
    print(f'{len(cases)} complete envelopes parsed; C/Lean bytes equal')
