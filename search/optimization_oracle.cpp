// Floating-point search kernel derived from the repository's exact raw oracle.
// It is not part of the certificate verifier or Lean trusted computation.
#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <thread>
#include <vector>
using namespace std;
static vector<array<int,3>> triples(int n){vector<array<int,3>>v;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)for(int k=j+1;k<n;k++)v.push_back({i,j,k});return v;}
static vector<array<int,6>> perms6(){vector<array<int,6>>ps;array<int,6>p={0,1,2,3,4,5};do ps.push_back(p);while(next_permutation(p.begin(),p.end()));return ps;}

struct Emb { uint64_t mask; array<uint16_t,1024> lut; };
struct Event { uint16_t a,b; uint8_t sigma; };
struct Setup { vector<Emb> emb; vector<Event> ev; int d[2]; };
static uint16_t permute5swap(uint16_t m,const vector<array<int,3>>&t5,int ix5[5][5][5]){
 uint16_t out=0;int p[5]={0,1,2,4,3};for(int i=0;i<10;i++)if((m>>i)&1){auto e=t5[i];array<int,3>z={p[e[0]],p[e[1]],p[e[2]]};sort(z.begin(),z.end());out|=1u<<ix5[z[0]][z[1]][z[2]];}return out;
}
static bool k4free5(uint16_t m,const vector<array<int,3>>&t5,int ix5[5][5][5]){for(int a=0;a<5;a++)for(int b=a+1;b<5;b++)for(int c=b+1;c<5;c++)for(int d=c+1;d<5;d++){int cnt=0;array<int,4>q={a,b,c,d};for(int r=0;r<4;r++){array<int,3>e{};int z=0;for(int s=0;s<4;s++)if(s!=r)e[z++]=q[s];if((m>>ix5[e[0]][e[1]][e[2]])&1)cnt++;}if(cnt==4)return false;}return true;}
static Setup build_s3(){
 Setup S;auto t5=triples(5),t7=triples(7);int ix5[5][5][5],ix7[7][7][7];fill(&ix5[0][0][0],&ix5[0][0][0]+125,-1);fill(&ix7[0][0][0],&ix7[0][0][0]+343,-1);for(int i=0;i<10;i++){auto e=t5[i];ix5[e[0]][e[1]][e[2]]=i;}for(int i=0;i<35;i++){auto e=t7[i];ix7[e[0]][e[1]][e[2]]=i;}
 vector<uint16_t> flags[2];array<int16_t,1024> id[2];id[0].fill(-1);id[1].fill(-1);
 for(int sig=0;sig<2;sig++){vector<uint16_t>tmp;for(uint16_t m=0;m<1024;m++){if(((m>>ix5[0][1][2])&1)!=sig||!k4free5(m,t5,ix5))continue;uint16_t c=min(m,permute5swap(m,t5,ix5));tmp.push_back(c);}sort(tmp.begin(),tmp.end());tmp.erase(unique(tmp.begin(),tmp.end()),tmp.end());flags[sig]=tmp;for(int i=0;i<(int)tmp.size();i++)id[sig][tmp[i]]=i;S.d[sig]=tmp.size();}
 int embix[7][7][7][7][7];fill(&embix[0][0][0][0][0],&embix[0][0][0][0][0]+16807,-1);
 for(int r0=0;r0<7;r0++)for(int r1=0;r1<7;r1++)if(r1!=r0)for(int r2=0;r2<7;r2++)if(r0<r1&&r1<r2){vector<int>rem;for(int v=0;v<7;v++)if(v!=r0&&v!=r1&&v!=r2)rem.push_back(v);for(int aa=0;aa<4;aa++)for(int bb=aa+1;bb<4;bb++){int u=rem[aa],v=rem[bb];Emb E{};array<int,5>vert={r0,r1,r2,u,v};vector<pair<int,int>>pos;uint64_t mask=0;for(int li=0;li<10;li++){auto e=t5[li];array<int,3>g={vert[e[0]],vert[e[1]],vert[e[2]]};sort(g.begin(),g.end());int gi=ix7[g[0]][g[1]][g[2]];mask|=1ULL<<gi;pos.push_back({gi,li});}sort(pos.begin(),pos.end());E.mask=mask;for(int bits=0;bits<1024;bits++){uint16_t lm=0;for(int p=0;p<10;p++)if((bits>>p)&1)lm|=1u<<pos[p].second;int sig=(lm>>ix5[0][1][2])&1;uint16_t c=min(lm,permute5swap(lm,t5,ix5));int z=id[sig][c];E.lut[bits]=(z<0?65535:(uint16_t)z);}int idx=S.emb.size();S.emb.push_back(E);embix[r0][r1][r2][min(u,v)][max(u,v)]=idx;}}
 for(int r0=0;r0<7;r0++)for(int r1=0;r1<7;r1++)if(r1!=r0)for(int r2=0;r2<7;r2++)if(r0<r1&&r1<r2){vector<int>rem;for(int v=0;v<7;v++)if(v!=r0&&v!=r1&&v!=r2)rem.push_back(v);for(int b=1;b<4;b++){int u=rem[0],v=rem[b];vector<int>other;for(int x:rem)if(x!=u&&x!=v)other.push_back(x);int e1=embix[r0][r1][r2][min(u,v)][max(u,v)],e2=embix[r0][r1][r2][min(other[0],other[1])][max(other[0],other[1])];array<int,3>root={r0,r1,r2};sort(root.begin(),root.end());int sigbit=ix7[root[0]][root[1]][root[2]];S.ev.push_back({(uint16_t)e1,(uint16_t)e2,(uint8_t)sigbit});}}
 return S;
}
static inline uint64_t _pext_u64(uint64_t v,uint64_t mask){
 uint64_t out=0,b=1;while(mask){uint64_t z=mask&-mask;if(v&z)out|=b;mask&=mask-1;b<<=1;}return out;
}
static inline int flagid(const Emb&E,uint64_t m){int z=E.lut[_pext_u64(m,E.mask)];if(z==65535){cerr<<"bad induced flag\n";exit(6);}return z;}


#include "optimization_oracle_tail.inc"
