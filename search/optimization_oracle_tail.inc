// Shared setup and C entry points; included after the inherited flag routines.
struct Oracle {
 Setup ss=build_s3();
 vector<uint32_t> reps;
 vector<int16_t> canon;
 int ix6[6][6][6], ix7[7][7][7];
 vector<array<int,3>> t6=triples(6),t7=triples(7);
 vector<pair<int,int>> pairs;
 int pairix[6][6];
 vector<uint32_t> ext[6],base[6];
 vector<uint64_t> ext7,base7;
 vector<vector<uint16_t>> links;
 struct PI {uint64_t fu,ru,fv,rv;};
 vector<PI> pis;
 int ut[7][7];
 Oracle(const uint32_t* input,int n):reps(input,input+n),canon(1<<20,-1){
  for(int i=0;i<20;i++){auto e=t6[i];ix6[e[0]][e[1]][e[2]]=i;}
  for(int i=0;i<35;i++){auto e=t7[i];ix7[e[0]][e[1]][e[2]]=i;}
  for(auto&p:perms6())for(int h=0;h<n;h++){
   uint32_t z=0;for(int i=0;i<20;i++)if((reps[h]>>i)&1){auto e=t6[i];array<int,3> q={p[e[0]],p[e[1]],p[e[2]]};sort(q.begin(),q.end());z|=1u<<ix6[q[0]][q[1]][q[2]];}canon[z]=h;
  }
  for(int i=0;i<6;i++)for(int j=i+1;j<6;j++){pairix[i][j]=pairix[j][i]=pairs.size();pairs.push_back({i,j});}
  ext7.resize(1<<15);base7.resize(n);links.resize(n);
  for(int am=0;am<(1<<15);am++)for(int p=0;p<15;p++)if((am>>p)&1){auto [a,b]=pairs[p];ext7[am]|=1ULL<<ix7[a][b][6];}
  for(int h=0;h<n;h++){
   vector<char>allow(1<<15,1);
   for(int i=0;i<20;i++)if((reps[h]>>i)&1){auto e=t6[i];base7[h]|=1ULL<<ix7[e[0]][e[1]][e[2]];
    uint16_t f=(1u<<pairix[e[0]][e[1]])|(1u<<pairix[e[0]][e[2]])|(1u<<pairix[e[1]][e[2]]),rest=((1u<<15)-1)^f;
    for(uint16_t sub=rest;;sub=(sub-1)&rest){allow[f|sub]=0;if(!sub)break;}
   }
   for(int am=0;am<(1<<15);am++)if(allow[am])links[h].push_back(am);
  }
  for(int del=0;del<6;del++){
   vector<int> vs;for(int v=0;v<6;v++)if(v!=del)vs.push_back(v);vs.push_back(6);
   ext[del].resize(1<<15);base[del].resize(n);
   for(int am=0;am<(1<<15);am++)for(int a=0;a<5;a++)for(int b=a+1;b<5;b++)if((am>>pairix[vs[a]][vs[b]])&1)ext[del][am]|=1u<<ix6[a][b][5];
   for(int h=0;h<n;h++)for(int i=0;i<20;i++)if((reps[h]>>i)&1){auto e=t6[i];if(e[0]==del||e[1]==del||e[2]==del)continue;
    int a=find(vs.begin(),vs.end(),e[0])-vs.begin(),b=find(vs.begin(),vs.end(),e[1])-vs.begin(),c=find(vs.begin(),vs.end(),e[2])-vs.begin();base[del][h]|=1u<<ix6[a][b][c];
   }
  }
  int pos=0;for(int i=0;i<7;i++)for(int j=i;j<7;j++)ut[i][j]=ut[j][i]=pos++;
  for(int root=0;root<7;root++){
   vector<int>rem;for(int v=0;v<7;v++)if(v!=root)rem.push_back(v);
   for(int b=1;b<6;b++)for(int c=b+1;c<6;c++){
    array<int,3>U={rem[0],rem[b],rem[c]},V{};int vi=0;
    for(int x:rem)if(find(U.begin(),U.end(),x)==U.end())V[vi++]=x;
    auto mf=[&](array<int,3>W){uint64_t fm=1ULL<<ix7[W[0]][W[1]][W[2]],rm=0;
     for(int i=0;i<3;i++)for(int j=i+1;j<3;j++){array<int,3>e={root,W[i],W[j]};sort(e.begin(),e.end());rm|=1ULL<<ix7[e[0]][e[1]][e[2]];}
     return pair<uint64_t,uint64_t>{fm,rm};};
    auto u=mf(U),v=mf(V);pis.push_back({u.first,u.second,v.first,v.second});
   }
  }
 }
 int cat(uint64_t m,uint64_t fm,uint64_t rm)const{return (m&fm?4:0)+__builtin_popcountll(m&rm);}
 void deck(uint64_t m,uint16_t*out)const{
  for(int del=0;del<7;del++){int vs[6],k=0;for(int v=0;v<7;v++)if(v!=del)vs[k++]=v;uint32_t z=0;
   for(int i=0;i<20;i++){auto e=t6[i];if((m>>ix7[vs[e[0]]][vs[e[1]]][vs[e[2]]])&1)z|=1u<<i;}out[del]=canon[z];
  }
 }
 void features(uint64_t m,uint16_t*one,uint32_t*three)const{
  fill(one,one+28,0);
  for(auto&z:pis){int a=cat(m,z.fu,z.ru),b=cat(m,z.fv,z.rv);one[ut[a][b]]++;}
  for(int k=0;k<(int)ss.ev.size();k++){auto&e=ss.ev[k];int sig=(m>>e.sigma)&1,i=flagid(ss.emb[e.a],m),j=flagid(ss.emb[e.b],m);three[k]=(sig?236*236:0)+i*ss.d[sig]+j;}
 }
 double value(uint64_t m,const double*q1,const double*q3)const{
  double z=0;for(auto&p:pis)z+=q1[ut[cat(m,p.fu,p.ru)][cat(m,p.fv,p.rv)]];
  for(auto&e:ss.ev){int sig=(m>>e.sigma)&1,i=flagid(ss.emb[e.a],m),j=flagid(ss.emb[e.b],m);z+=q3[(sig?236*236:0)+i*ss.d[sig]+j];}return z;
 }
};
static Oracle* oracle=nullptr;
extern "C" {
int initialize(const uint32_t*reps,int n){if(oracle)delete oracle;oracle=new Oracle(reps,n);int total=0;for(auto&v:oracle->links)total+=v.size();return total;}
void get_features(const uint64_t*m,int n,uint16_t*decks,uint16_t*one,uint32_t*three){for(int i=0;i<n;i++){oracle->deck(m[i],decks+7*i);oracle->features(m[i],one+28*i,three+105*i);}}
// Each class returns its k largest values. All 13,051,375 raw columns are scanned.
void price(const double*six,const double*q1,const double*q3,int nth,int k,double*values,uint64_t*masks){
 atomic<int>next{0};vector<thread>workers;
 for(int t=0;t<nth;t++)workers.emplace_back([&]{for(int h;(h=next++)<(int)oracle->reps.size();){
  vector<pair<double,uint64_t>>best;best.reserve(k);
  for(int am:oracle->links[h]){double z=six[h];for(int d=0;d<6;d++)z+=six[oracle->canon[oracle->base[d][h]|oracle->ext[d][am]]];
   uint64_t m=oracle->base7[h]|oracle->ext7[am];z+=oracle->value(m,q1,q3);
   if((int)best.size()<k){best.push_back({z,m});push_heap(best.begin(),best.end(),greater<pair<double,uint64_t>>());}
   else if(z>best.front().first){pop_heap(best.begin(),best.end(),greater<pair<double,uint64_t>>());best.back()={z,m};push_heap(best.begin(),best.end(),greater<pair<double,uint64_t>>());}
  }
  sort(best.rbegin(),best.rend());for(int j=0;j<k;j++){values[h*k+j]=j<(int)best.size()?best[j].first:-INFINITY;masks[h*k+j]=j<(int)best.size()?best[j].second:0;}
 }});for(auto&t:workers)t.join();
}
}

#include "optimization_order8.inc"
