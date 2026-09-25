# Simulate conveyor: segment of m tiles in row r moving left by D cells, lane row r'.
# Track net displacement of every tile.
import sys
def run(m, D, W=None):
    W = W or (m+D+4)
    # grid rows 0 (segment row) and 1 (lane), columns 0..W-1
    grid = {}
    pos = {}
    t=1
    for r in range(2):
        for c in range(W):
            grid[(r,c)] = t; pos[t]=(r,c); t+=1
    # segment at columns e+D+1..e+D+m, e=0; blank at (0,D)
    e=0
    b=(0,e+D)
    blank_tile=grid[b]
    seg=[grid[(0,e+D+1+i)] for i in range(m)]
    start={tile:p for p,tile in grid.items()}
    moves=0
    def mv(to):
        nonlocal b,moves
        tl=grid[to]; grid[b]=tl; grid[to]=blank_tile; b=to; moves+=1
    for step in range(D):
        ee=e+D-1-step  # blank at (0,ee+1)
        # walk right through segment
        for i in range(m): mv((0,ee+2+i))
        mv((1,ee+1+m))
        for i in range(m+1): mv((1,ee+m-i))
        mv((0,ee))
    disp={}
    for p,tile in grid.items():
        if tile==blank_tile: continue
        s=start[tile]; disp[tile]=(p[0]-s[0],p[1]-s[1])
    segd=sum(abs(disp[x][0])+abs(disp[x][1]) for x in seg)
    other=[x for x in disp if x not in seg]
    od=sum(abs(disp[x][0])+abs(disp[x][1]) for x in other)
    moved=sum(1 for x in other if disp[x]!=(0,0))
    return moves, segd, od, moved
for m,D in [(10,10),(10,50),(50,10),(100,300),(300,100)]:
    print(m,D,run(m,D))
