#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <immintrin.h>
#include <iostream>
#include <limits>
#include <numeric>
#include <string>
#include <vector>
#include <omp.h>
using namespace std;

static string i128str(__int128 x){ if(x==0)return "0"; bool neg=x<0;if(neg)x=-x;string s;while(x){s.push_back('0'+x%10);x/=10;}if(neg)s.push_back('-');reverse(s.begin(),s.end());return s; }
static long double i128ld(__int128 x){ return (long double)x; }
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
 for(int r0=0;r0<7;r0++)for(int r1=0;r1<7;r1++)if(r1!=r0)for(int r2=0;r2<7;r2++)if(r2!=r0&&r2!=r1){vector<int>rem;for(int v=0;v<7;v++)if(v!=r0&&v!=r1&&v!=r2)rem.push_back(v);for(int aa=0;aa<4;aa++)for(int bb=aa+1;bb<4;bb++){int u=rem[aa],v=rem[bb];Emb E{};array<int,5>vert={r0,r1,r2,u,v};vector<pair<int,int>>pos;uint64_t mask=0;for(int li=0;li<10;li++){auto e=t5[li];array<int,3>g={vert[e[0]],vert[e[1]],vert[e[2]]};sort(g.begin(),g.end());int gi=ix7[g[0]][g[1]][g[2]];mask|=1ULL<<gi;pos.push_back({gi,li});}sort(pos.begin(),pos.end());E.mask=mask;for(int bits=0;bits<1024;bits++){uint16_t lm=0;for(int p=0;p<10;p++)if((bits>>p)&1)lm|=1u<<pos[p].second;int sig=(lm>>ix5[0][1][2])&1;uint16_t c=min(lm,permute5swap(lm,t5,ix5));int z=id[sig][c];E.lut[bits]=(z<0?65535:(uint16_t)z);}int idx=S.emb.size();S.emb.push_back(E);embix[r0][r1][r2][min(u,v)][max(u,v)]=idx;}}
 for(int r0=0;r0<7;r0++)for(int r1=0;r1<7;r1++)if(r1!=r0)for(int r2=0;r2<7;r2++)if(r2!=r0&&r2!=r1){vector<int>rem;for(int v=0;v<7;v++)if(v!=r0&&v!=r1&&v!=r2)rem.push_back(v);for(int b=1;b<4;b++){int u=rem[0],v=rem[b];vector<int>other;for(int x:rem)if(x!=u&&x!=v)other.push_back(x);int e1=embix[r0][r1][r2][min(u,v)][max(u,v)],e2=embix[r0][r1][r2][min(other[0],other[1])][max(other[0],other[1])];array<int,3>root={r0,r1,r2};sort(root.begin(),root.end());int sigbit=ix7[root[0]][root[1]][root[2]];S.ev.push_back({(uint16_t)e1,(uint16_t)e2,(uint8_t)sigbit});}}
 return S;
}
static inline int flagid(const Emb&E,uint64_t m){int z=E.lut[_pext_u64(m,E.mask)];if(z==65535){cerr<<"bad induced flag\n";exit(6);}return z;}

struct ThreadBest{__int128 num;uint64_t mask,count;array<uint16_t,7>deck;ThreadBest():num(-((__int128)1<<120)),mask(0),count(0){}};

int main(int argc,char**argv){
 if(argc<6){cerr<<"usage: full_reps.txt support_full_ids.txt candidate.bin output.txt threads\n";return 2;}
 int nth=stoi(argv[5]);if(nth>0)omp_set_num_threads(nth);
 vector<uint32_t> reps;{ifstream f(argv[1]);uint64_t x;while(f>>x)reps.push_back((uint32_t)x);}vector<int>Sids;vector<int16_t>supportIndex(reps.size(),-1);{ifstream f(argv[2]);int x;while(f>>x){supportIndex[x]=Sids.size();Sids.push_back(x);}}
 ifstream cf(argv[3],ios::binary);uint64_t D;int64_t tau;uint32_t ncls,d0,d1;cf.read((char*)&D,8);cf.read((char*)&tau,8);cf.read((char*)&ncls,4);cf.read((char*)&d0,4);cf.read((char*)&d1,4);vector<int64_t>classnum(ncls),q1(28),Q0((size_t)d0*d0),Q1((size_t)d1*d1);cf.read((char*)classnum.data(),classnum.size()*8);cf.read((char*)q1.data(),q1.size()*8);cf.read((char*)Q0.data(),Q0.size()*8);cf.read((char*)Q1.data(),Q1.size()*8);if(!cf){cerr<<"bad candidate file\n";return 3;}if(ncls!=Sids.size()){cerr<<"ncls mismatch\n";return 4;}
 Setup SS=build_s3();if((uint32_t)SS.d[0]!=d0||(uint32_t)SS.d[1]!=d1){cerr<<"dims mismatch\n";return 5;}
 auto t6=triples(6),t7=triples(7);int ix6[6][6][6],ix7[7][7][7];fill(&ix6[0][0][0],&ix6[0][0][0]+216,-1);fill(&ix7[0][0][0],&ix7[0][0][0]+343,-1);for(int i=0;i<(int)t6.size();i++){auto e=t6[i];ix6[e[0]][e[1]][e[2]]=i;}for(int i=0;i<(int)t7.size();i++){auto e=t7[i];ix7[e[0]][e[1]][e[2]]=i;}
 vector<int16_t>canon(1<<20,-1);auto ps=perms6();vector<array<int,20>>maps;for(auto&p:ps){array<int,20>mp{};for(int i=0;i<20;i++){auto e=t6[i];array<int,3>z={p[e[0]],p[e[1]],p[e[2]]};sort(z.begin(),z.end());mp[i]=ix6[z[0]][z[1]][z[2]];}maps.push_back(mp);}for(int r=0;r<(int)reps.size();r++)for(auto&mp:maps){uint32_t z=0,m=reps[r];while(m){int i=__builtin_ctz(m);z|=1u<<mp[i];m&=m-1;}canon[z]=r;} for(int z=0;z<(1<<20);z++)if(canon[z]<0){cerr<<"incomplete six-vertex representative list at mask "<<z<<"\n";return 7;}
 vector<pair<int,int>>pairs;int pairix[6][6];fill(&pairix[0][0],&pairix[0][0]+36,-1);for(int i=0;i<6;i++)for(int j=i+1;j<6;j++){pairix[i][j]=pairix[j][i]=pairs.size();pairs.push_back({i,j});}
 vector<array<uint32_t,6>>basepart(reps.size());static uint32_t extpart[6][1<<15];for(int del=0;del<6;del++){vector<int>vs;for(int v=0;v<6;v++)if(v!=del)vs.push_back(v);vs.push_back(6);for(int am=0;am<(1<<15);am++){uint32_t z=0;for(int a=0;a<5;a++)for(int b=a+1;b<5;b++){int oa=vs[a],ob=vs[b];if((am>>pairix[oa][ob])&1)z|=1u<<ix6[a][b][5];}extpart[del][am]=z;}for(int ri:Sids){uint32_t z=0,m=reps[ri];for(int li=0;li<20;li++)if((m>>li)&1){auto e=t6[li];if(e[0]==del||e[1]==del||e[2]==del)continue;int a=find(vs.begin(),vs.end(),e[0])-vs.begin(),b=find(vs.begin(),vs.end(),e[1])-vs.begin(),c=find(vs.begin(),vs.end(),e[2])-vs.begin();array<int,3>q={a,b,c};sort(q.begin(),q.end());z|=1u<<ix6[q[0]][q[1]][q[2]];}basepart[ri][del]=z;}}
 int ut[7][7],pos=0;for(int i=0;i<7;i++)for(int j=i;j<7;j++)ut[i][j]=ut[j][i]=pos++;
 struct PI{uint64_t fu,ru,fv,rv;};vector<PI>pis;for(int root=0;root<7;root++){vector<int>rem;for(int v=0;v<7;v++)if(v!=root)rem.push_back(v);for(int b=1;b<6;b++)for(int c=b+1;c<6;c++){array<int,3>U={rem[0],rem[b],rem[c]};bool in[7]={};for(int x:U)in[x]=1;array<int,3>V{};int vi=0;for(int x:rem)if(!in[x])V[vi++]=x;auto mf=[&](array<int,3>W){sort(W.begin(),W.end());uint64_t fm=1ULL<<ix7[W[0]][W[1]][W[2]],rm=0;for(int i=0;i<3;i++)for(int j=i+1;j<3;j++){array<int,3>e={root,W[i],W[j]};sort(e.begin(),e.end());rm|=1ULL<<ix7[e[0]][e[1]][e[2]];}return pair<uint64_t,uint64_t>{fm,rm};};auto u=mf(U),v=mf(V);pis.push_back({u.first,u.second,v.first,v.second});}}
 auto cat=[&](uint64_t m,uint64_t fm,uint64_t rm){int f=(m&fm)?1:0,k=__builtin_popcountll(m&rm);return f?4+k:k;};
 vector<ThreadBest> best(omp_get_max_threads());
#pragma omp parallel for schedule(dynamic,1)
 for(long long si=0;si<(long long)Sids.size();si++){
  int tid=omp_get_thread_num(),ri=Sids[si];uint32_t H=reps[ri];vector<uint16_t>forb;for(int i=0;i<20;i++)if((H>>i)&1){auto e=t6[i];forb.push_back((1u<<pairix[e[0]][e[1]])|(1u<<pairix[e[0]][e[2]])|(1u<<pairix[e[1]][e[2]]));}vector<char>allow(1<<15,1);for(uint16_t f:forb){uint16_t rest=((1u<<15)-1)^f;for(uint16_t sub=rest;;sub=(sub-1)&rest){allow[f|sub]=0;if(!sub)break;}}
  uint64_t base7=0;for(int i=0;i<20;i++)if((H>>i)&1){auto e=t6[i];base7|=1ULL<<ix7[e[0]][e[1]][e[2]];}
  for(int am=0;am<(1<<15);am++)if(allow[am]){
   array<uint16_t,7>deck{};bool ok=true;__int128 num=0;for(int del=0;del<6;del++){int fid=canon[basepart[ri][del]|extpart[del][am]],sid=(fid>=0?supportIndex[fid]:-1);if(sid<0){ok=false;break;}deck[del]=sid;num+=classnum[sid];}if(!ok)continue;int sri=supportIndex[ri];deck[6]=sri;num+=classnum[sri];
   uint64_t m7=base7;for(int pi=0;pi<15;pi++)if((am>>pi)&1){auto [a,b]=pairs[pi];m7|=1ULL<<ix7[a][b][6];}
   array<uint16_t,28>feat{};for(auto&z:pis){int aa=cat(m7,z.fu,z.ru),bb=cat(m7,z.fv,z.rv);feat[ut[aa][bb]]+=2;}for(int k=0;k<28;k++)num+=(__int128)36*feat[k]*q1[k];
   for(auto&e:SS.ev){int sig=(m7>>e.sigma)&1,i=flagid(SS.emb[e.a],m7),j=flagid(SS.emb[e.b],m7);num+=(__int128)8*(sig?Q1[(size_t)i*d1+j]:Q0[(size_t)i*d0+j]);}
   best[tid].count++;if(num>best[tid].num){best[tid].num=num;best[tid].mask=m7;best[tid].deck=deck;}
  }
 }
 ThreadBest ans;uint64_t total=0;for(auto&b:best){total+=b.count;if(b.num>ans.num)ans=b;}__int128 den=(__int128)5040*D*D;
 ofstream o(argv[4]);o<<"raw_count "<<total<<"\nmax_numerator "<<i128str(ans.num)<<"\ndenominator "<<i128str(den)<<"\nmax_mask "<<ans.mask<<"\ndecimal "<<(double)(i128ld(ans.num)/i128ld(den))<<"\n";o<<"deck";for(auto z:ans.deck)o<<" "<<z;o<<"\n";
 cerr<<"raw "<<total<<" max "<<i128str(ans.num)<<" / "<<i128str(den)<<" = "<<(double)(i128ld(ans.num)/i128ld(den))<<" mask "<<ans.mask<<"\n";
}
