import sys
def sim(m):
    # board 3 x m, tiles labeled by initial position; blank at (2,0)
    B={(r,c):(r,c) for r in range(3) for c in range(m)}
    b=(2,0); B[b]=None
    # tile-direction semantics: tile moves in dir, blank opposite
    mv={'L':(0,1),'R':(0,-1),'U':(1,0),'D':(-1,0)}  # blank displacement
    word=list('LDRD')+['L']*(m-1)+list('RULDR')*(m-2)+list('UURDDLURU')
    for w in word:
        dr,dc=mv[w]; nb=(b[0]+dr,b[1]+dc)
        assert nb in B, (w,b)
        B[b]=B[nb]; B[nb]=None; b=nb
    assert b==(2,0)
    disp=0; out={}
    for pos,t in B.items():
        if t is None: continue
        d=abs(pos[0]-t[0])+abs(pos[1]-t[1]); disp+=d
        if d: out[t]=pos
    return len(word),disp,out
for m in [3,4,5,8]:
    L,D,o=sim(m); print(m,L,D, sorted(o.items())[:12])
