// Optimal 15-puzzle solver: IDA* with additive 5-5-5 pattern databases (+ transposed lookup).
// Target: tile t at cell t-1 (row-major), blank at cell 15.
// Input: lines of 16 ints (row-major, 0 = blank). Output: OPT and Manhattan.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define N 4
#define NN 16
static const int parts[3][5] = {{1,2,3,5,6},{4,7,8,11,12},{9,10,13,14,15}};
static uint8_t *pdb[3];
static int partOf[NN], idxIn[NN];
static int nbr[NN][4], nnbr[NN];
static int transCell[NN];   // transpose of cell
static int transTile[NN];   // tile whose goal is the transpose of goal of t

static inline int goal(int t){ return t-1; }

static void build(int p){
  // state index: pos[0..4] base16, then blank (4 bits) => 2^24
  size_t S = 1u<<24;
  uint8_t *d = malloc(S); memset(d, 255, S);
  uint32_t *q = malloc(sizeof(uint32_t)*S*2); // deque as ring buffer
  size_t cap = S*2, head = cap*1000, tail = cap*1000; // [head, tail), indices kept in [0, 3cap)
  // goal: tiles at goal cells, blank anywhere not occupied => 0
  int pos[5]; for(int i=0;i<5;i++) pos[i]=goal(parts[p][i]);
  uint32_t base=0; for(int i=0;i<5;i++) base |= (uint32_t)pos[i]<<(4*i);
  for(int b=0;b<NN;b++){ int occ=0; for(int i=0;i<5;i++) if(pos[i]==b) occ=1; if(occ) continue;
    uint32_t s = base | ((uint32_t)b<<20); d[s]=0; q[tail++ % cap]=s; }
  while(head!=tail){
    uint32_t s = q[head++ % cap];
    int dv = d[s];
    int b = (s>>20)&15; int ps[5]; for(int i=0;i<5;i++) ps[i]=(s>>(4*i))&15;
    for(int k=0;k<nnbr[b];k++){ int c=nbr[b][k]; int who=-1; for(int i=0;i<5;i++) if(ps[i]==c) who=i;
      uint32_t t; int w;
      if(who<0){ t = (s & 0xFFFFF) | ((uint32_t)c<<20); w=0; }
      else { t = (s & ~(0xFu<<(4*who)) & 0xFFFFF) | ((uint32_t)b<<(4*who)) | ((uint32_t)c<<20); w=1; }
      if(d[t] > dv+w){ d[t]=dv+w; if(w==0){ head--; q[head % cap]=t; } else q[tail++ % cap]=t; if(tail-head>=cap){fprintf(stderr,"overflow\n");exit(1);} }
    }
  }
  pdb[p] = malloc(1u<<20); memset(pdb[p],255,1u<<20);
  for(size_t s=0;s<S;s++){ uint32_t k = s & 0xFFFFF; if(d[s]<pdb[p][k]) pdb[p][k]=d[s]; }
  free(d); free(q);
}

static int board[NN], posOf[NN], blank;

static int h(void){
  int v=0, vt=0;
  for(int p=0;p<3;p++){
    uint32_t k=0, kt=0;
    for(int i=0;i<5;i++){ int t=parts[p][i]; k |= (uint32_t)posOf[t]<<(4*i);
      // transposed lookup: tile t' = transTile[t] sits at transCell[posOf[t]]; pattern p of reflected state
    }
    v += pdb[p][k];
    for(int i=0;i<5;i++){ int t=parts[p][i]; int src = transTile[t]; kt |= (uint32_t)transCell[posOf[src]]<<(4*i); }
    vt += pdb[p][kt];
  }
  return v>vt? v: vt;
}

static long long nodes;
static int bound_;
static int search(int g, int prev){
  int hv = h(); int f = g+hv;
  if(f>bound_) return f;
  if(hv==0) return -1;
  int mn = 1<<30;
  int b = blank;
  for(int k=0;k<nnbr[b];k++){ int c=nbr[b][k]; if(c==prev) continue;
    int t=board[c]; board[b]=t; posOf[t]=b; board[c]=0; blank=c; nodes++;
    int r = search(g+1, b);
    board[c]=t; posOf[t]=c; board[b]=0; blank=b;
    if(r<0) return -1; if(r<mn) mn=r;
  }
  return mn;
}

int main(void){
  for(int c=0;c<NN;c++){ int x=c/N,y=c%N; nnbr[c]=0;
    if(x>0) nbr[c][nnbr[c]++]=c-N; if(x<N-1) nbr[c][nnbr[c]++]=c+N;
    if(y>0) nbr[c][nnbr[c]++]=c-1; if(y<N-1) nbr[c][nnbr[c]++]=c+1;
    transCell[c]=y*N+x; }
  for(int t=1;t<NN;t++){ transTile[t] = transCell[goal(t)]+1; }
  for(int p=0;p<3;p++) build(p);
  fprintf(stderr,"pdb built\n");
  int in[NN];
  while(1){
    for(int i=0;i<NN;i++) if(scanf("%d",&in[i])!=1) return 0;
    int M=0; for(int c=0;c<NN;c++){ board[c]=in[c]; posOf[in[c]]=c; if(in[c]==0) blank=c; else { int g=goal(in[c]); M+=abs(g/N-c/N)+abs(g%N-c%N);} }
    nodes=0; bound_=h(); int h0=bound_;
    while(1){ int r=search(0,-1); if(r<0) break; bound_=r; }
    printf("OPT %d M %d I %d h0 %d nodes %lld\n", bound_, M, (bound_-M)/2, h0, nodes);
    fflush(stdout);
  }
}
