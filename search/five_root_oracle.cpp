// Additional (s,l)=(5,6) blocks on the complete seven-vertex universe.
// This numerical/integer research oracle is independent of Lean's checker.
#include "optimization_oracle.cpp"
#include <limits>
#include <stdexcept>

struct FiveEmbedding { array<array<uint32_t,128>,5> lut{}; };
struct FiveOracle {
 vector<FiveEmbedding> embeddings;
 array<int16_t,1024> type{};
 array<uint8_t,1024> canon_perm{};
 vector<uint16_t> pair_perm;
 vector<int16_t> flag_ids;
 vector<int> dims;
 vector<uint64_t> offsets;
 FiveOracle(const int16_t *types,const uint8_t *cp,const uint16_t *pp,
            const int16_t *fi,const int *ds,int n):pair_perm(pp,pp+120*1024),
            flag_ids(fi,fi+n*1024),dims(ds,ds+n),offsets(n+1,0){
  copy(types,types+1024,type.begin());copy(cp,cp+1024,canon_perm.begin());
  for(int i=0;i<n;i++)offsets[i+1]=offsets[i]+uint64_t(dims[i])*dims[i];
  auto t5=triples(5);vector<pair<int,int>> pairs5;
  for(int i=0;i<5;i++)for(int j=i+1;j<5;j++)pairs5.push_back({i,j});
  for(int u=0;u<7;u++)for(int v=u+1;v<7;v++){
   array<int,5> roots{};int z=0;for(int a=0;a<7;a++)if(a!=u&&a!=v)roots[z++]=a;
   array<int,35> dest;dest.fill(-1);
   for(int j=0;j<10;j++){
    auto e=t5[j];dest[oracle->ix7[roots[e[0]]][roots[e[1]]][roots[e[2]]]]=j;
    auto [a,b]=pairs5[j];array<int,3> ea={roots[a],roots[b],u},eb={roots[a],roots[b],v};
    sort(ea.begin(),ea.end());sort(eb.begin(),eb.end());
    dest[oracle->ix7[ea[0]][ea[1]][ea[2]]]=10+j;dest[oracle->ix7[eb[0]][eb[1]][eb[2]]]=20+j;
   }
   FiveEmbedding E;
   for(int chunk=0;chunk<5;chunk++)for(int bits=0;bits<128;bits++)
    for(int j=0;j<7;j++)if((bits>>j&1)&&dest[7*chunk+j]>=0)E.lut[chunk][bits]|=1u<<dest[7*chunk+j];
   embeddings.push_back(E);
  }
 }
 inline bool indices(uint64_t m,const FiveEmbedding&E,int &t,int &a,int &b)const{
  uint32_t z=E.lut[0][m&127]|E.lut[1][(m>>7)&127]|E.lut[2][(m>>14)&127]|
   E.lut[3][(m>>21)&127]|E.lut[4][(m>>28)&127];
  int root=z&1023;t=type[root];if(t<0)return false;int p=canon_perm[root]*1024;
  a=flag_ids[t*1024+pair_perm[p+((z>>10)&1023)]];
  b=flag_ids[t*1024+pair_perm[p+(z>>20)]];
  if(a<0||b<0)throw runtime_error("invalid five-root induced flag");return true;
 }
 double value(uint64_t m,const double*q)const{double sum=0;for(auto&E:embeddings){int t,a,b;if(indices(m,E,t,a,b))sum+=q[offsets[t]+uint64_t(a)*dims[t]+b];}return sum;}
 __int128 value_exact(uint64_t m,const int64_t*q)const{__int128 sum=0;for(auto&E:embeddings){int t,a,b;if(indices(m,E,t,a,b))sum+=q[offsets[t]+uint64_t(a)*dims[t]+b];}return sum;}
};
static FiveOracle* five=nullptr;
static __int128 inherited_exact(uint64_t m,const int64_t*q1,const int64_t*q3){
 __int128 z=0;for(auto&p:oracle->pis)z+=q1[oracle->ut[oracle->cat(m,p.fu,p.ru)][oracle->cat(m,p.fv,p.rv)]];
 for(auto&e:oracle->ss.ev){int sig=(m>>e.sigma)&1,i=flagid(oracle->ss.emb[e.a],m),j=flagid(oracle->ss.emb[e.b],m);z+=q3[(sig?236*236:0)+i*oracle->ss.d[sig]+j];}return z;
}
extern "C" {
void initialize_five(const int16_t*t,const uint8_t*cp,const uint16_t*pp,const int16_t*fi,const int*d,int n){if(five)delete five;five=new FiveOracle(t,cp,pp,fi,d,n);}
// Each row has 21 unordered rootsets. Unselected types use -1 and index 0.
void get_five_pairs(const uint64_t*m,int n,int16_t*types,uint32_t*pairs){
 for(int i=0;i<n;i++)for(int j=0;j<21;j++){int t=-1,a=0,b=0;bool ok=five->indices(m[i],five->embeddings[j],t,a,b);types[21*i+j]=t;pairs[21*i+j]=ok?a*five->dims[t]+b:0;}
}
void price_five(const double*six,const double*q1,const double*q3,const double*q5,int nth,int k,double*values,uint64_t*masks){
 atomic<int>next{0};vector<thread>workers;
 for(int t=0;t<nth;t++)workers.emplace_back([&]{for(int h;(h=next++)<(int)oracle->reps.size();){
  vector<pair<double,uint64_t>>best;best.reserve(k);
  for(int am:oracle->links[h]){double z=six[h];for(int d=0;d<6;d++)z+=six[oracle->canon[oracle->base[d][h]|oracle->ext[d][am]]];
   uint64_t m=oracle->base7[h]|oracle->ext7[am];z+=oracle->value(m,q1,q3)+five->value(m,q5);
   if((int)best.size()<k){best.push_back({z,m});push_heap(best.begin(),best.end(),greater<pair<double,uint64_t>>());}
   else if(make_pair(z,m)>best.front()){pop_heap(best.begin(),best.end(),greater<pair<double,uint64_t>>());best.back()={z,m};push_heap(best.begin(),best.end(),greater<pair<double,uint64_t>>());}
  }
  sort(best.rbegin(),best.rend());for(int j=0;j<k;j++){values[h*k+j]=j<(int)best.size()?best[j].first:-INFINITY;masks[h*k+j]=j<(int)best.size()?best[j].second:0;}
 }});for(auto&t:workers)t.join();
}
int eval_five_exact(const uint64_t*m,int n,const int64_t*six,const int64_t*q1,const int64_t*q3,const int64_t*q5,int64_t*out){
 for(int i=0;i<n;i++){uint16_t deck[7];oracle->deck(m[i],deck);__int128 z=0;for(int j=0;j<7;j++)z+=six[deck[j]];z+=inherited_exact(m[i],q1,q3)+five->value_exact(m[i],q5);
  if(z<numeric_limits<int64_t>::min()||z>numeric_limits<int64_t>::max())return 1;out[i]=(int64_t)z;}return 0;
}
int price_five_exact(const int64_t*six,const int64_t*q1,const int64_t*q3,const int64_t*q5,int nth,int k,int64_t*values,uint64_t*masks){
 atomic<int>next{0};atomic<int>overflow{0};vector<thread>workers;
 for(int t=0;t<nth;t++)workers.emplace_back([&]{for(int h;(h=next++)<(int)oracle->reps.size();){
  vector<pair<int64_t,uint64_t>>best;best.reserve(k);
  for(int am:oracle->links[h]){__int128 z=six[h];for(int d=0;d<6;d++)z+=six[oracle->canon[oracle->base[d][h]|oracle->ext[d][am]]];
   uint64_t m=oracle->base7[h]|oracle->ext7[am];z+=inherited_exact(m,q1,q3)+five->value_exact(m,q5);
   if(z<numeric_limits<int64_t>::min()||z>numeric_limits<int64_t>::max()){overflow=1;continue;}
   pair<int64_t,uint64_t> candidate={(int64_t)z,m};
   if((int)best.size()<k){best.push_back(candidate);push_heap(best.begin(),best.end(),greater<pair<int64_t,uint64_t>>());}
   else if(candidate>best.front()){pop_heap(best.begin(),best.end(),greater<pair<int64_t,uint64_t>>());best.back()=candidate;push_heap(best.begin(),best.end(),greater<pair<int64_t,uint64_t>>());}
  }
  sort(best.rbegin(),best.rend());for(int j=0;j<k;j++){values[h*k+j]=j<(int)best.size()?best[j].first:numeric_limits<int64_t>::min();masks[h*k+j]=j<(int)best.size()?best[j].second:0;}
 }});for(auto&t:workers)t.join();return overflow;
}
}
