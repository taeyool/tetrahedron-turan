// Selected order-eight extension: inherited seven-vertex blocks plus (s,l)=(0,4),(2,5).
struct Eight {
 struct E {uint64_t mask;array<uint16_t,1024>lut;};
 vector<E> emb;
 vector<pair<int,int>> events;
 vector<pair<uint64_t,uint64_t>> zero;
 vector<uint64_t> tetra;
 int ix8[8][8][8];
 vector<array<int,3>>t8=triples(8);
 array<int16_t,1024>canon;
 Eight(){
  for(int i=0;i<56;i++){auto e=t8[i];ix8[e[0]][e[1]][e[2]]=i;}
  auto t5=triples(5);int ix5[5][5][5];for(int i=0;i<10;i++){auto e=t5[i];ix5[e[0]][e[1]][e[2]]=i;}
  vector<int>flags;
  for(int m=0;m<1024;m++){
   int c=m;array<int,3>p={2,3,4};do{int pm[5]={0,1,p[0],p[1],p[2]},z=0;
    for(int i=0;i<10;i++)if((m>>i)&1){auto e=t5[i];array<int,3>v={pm[e[0]],pm[e[1]],pm[e[2]]};sort(v.begin(),v.end());z|=1<<ix5[v[0]][v[1]][v[2]];}c=min(c,z);
   }while(next_permutation(p.begin(),p.end()));canon[m]=c;
   if(c==m&&k4free5(m,t5,ix5))flags.push_back(m);
  }
  if(flags.size()!=174)abort();
  for(int m=0;m<1024;m++){int c=canon[m];auto it=lower_bound(flags.begin(),flags.end(),c);canon[m]=(it!=flags.end()&&*it==c)?it-flags.begin():-1;}
  for(int a=0;a<8;a++)for(int b=a+1;b<8;b++)for(int c=b+1;c<8;c++)for(int d=c+1;d<8;d++){
   array<int,4>u={a,b,c,d};uint64_t um=0;for(int r=0;r<4;r++){vector<int>v;for(int j=0;j<4;j++)if(j!=r)v.push_back(u[j]);um|=1ULL<<ix8[v[0]][v[1]][v[2]];}tetra.push_back(um);
   if(a!=0)continue;
   vector<int>w;for(int v=0;v<8;v++)if(find(u.begin(),u.end(),v)==u.end())w.push_back(v);uint64_t vm=0;
   for(int r=0;r<4;r++){vector<int>v;for(int j=0;j<4;j++)if(j!=r)v.push_back(w[j]);vm|=1ULL<<ix8[v[0]][v[1]][v[2]];}zero.push_back({um,vm});
  }
  for(int a=0;a<8;a++)for(int b=a+1;b<8;b++){
   vector<int>rem;for(int v=0;v<8;v++)if(v!=a&&v!=b)rem.push_back(v);
   for(int c=1;c<6;c++)for(int d=c+1;d<6;d++){
    array<int,3>u={rem[0],rem[c],rem[d]};vector<int>v;for(int x:rem)if(find(u.begin(),u.end(),x)==u.end())v.push_back(x);
    int first=emb.size();
    for(int part=0;part<2;part++){
     array<int,5>vs={a,b,part?v[0]:u[0],part?v[1]:u[1],part?v[2]:u[2]};E e{};vector<pair<int,int>>pos;
     for(int i=0;i<10;i++){auto q=t5[i];array<int,3>w={vs[q[0]],vs[q[1]],vs[q[2]]};sort(w.begin(),w.end());int gi=ix8[w[0]][w[1]][w[2]];e.mask|=1ULL<<gi;pos.push_back({gi,i});}sort(pos.begin(),pos.end());
     for(int bits=0;bits<1024;bits++){int m=0;for(int i=0;i<10;i++)if((bits>>i)&1)m|=1<<pos[i].second;e.lut[bits]=canon[m];}emb.push_back(e);
    }events.push_back({first,first+1});
   }
  }
 }
 bool valid(uint64_t m)const{for(auto q:tetra)if((m&q)==q)return false;return true;}
 uint64_t deletion(uint64_t m,int del)const{
  int vs[7],k=0;for(int v=0;v<8;v++)if(v!=del)vs[k++]=v;uint64_t out=0;
  for(int i=0;i<35;i++){auto e=oracle->t7[i];if((m>>ix8[vs[e[0]]][vs[e[1]]][vs[e[2]]])&1)out|=1ULL<<i;}return out;
 }
 double value(uint64_t m,const double*six,const double*q1,const double*q3,const double*q0,const double*q2)const{
  double z=0;uint16_t deck[7];
  for(int d=0;d<8;d++){auto m7=deletion(m,d);oracle->deck(m7,deck);for(auto h:deck)z+=six[h];z+=oracle->value(m7,q1,q3);}
  for(auto&e:zero)z+=q0[4*__builtin_popcountll(m&e.first)+__builtin_popcountll(m&e.second)];
  for(auto&e:events){int a=emb[e.first].lut[_pext_u64(m,emb[e.first].mask)],b=emb[e.second].lut[_pext_u64(m,emb[e.second].mask)];z+=q2[a*174+b];}return z;
 }
};
static Eight* eight=nullptr;
static uint64_t rng(uint64_t&s){s^=s<<13;s^=s>>7;s^=s<<17;return s;}
extern "C" {
void initialize8(){if(eight)delete eight;eight=new Eight();}
void get_features8(const uint64_t*m,int n,uint64_t*seven,uint16_t*zero,uint16_t*two){
 for(int i=0;i<n;i++){
  for(int d=0;d<8;d++)seven[i*8+d]=eight->deletion(m[i],d);
  fill(zero+i*16,zero+(i+1)*16,0);
  for(auto&e:eight->zero){int a=__builtin_popcountll(m[i]&e.first),b=__builtin_popcountll(m[i]&e.second);zero[i*16+a*4+b]++;zero[i*16+b*4+a]++;}
  for(int k=0;k<280;k++){auto&e=eight->events[k];int a=eight->emb[e.first].lut[_pext_u64(m[i],eight->emb[e.first].mask)],b=eight->emb[e.second].lut[_pext_u64(m[i],eight->emb[e.second].mask)];two[i*280+k]=a*174+b;}
 }
}
// Deterministic multistart local pricing. This is deliberately NOT a global oracle.
void heuristic8(const double*six,const double*q1,const double*q3,const double*q0,const double*q2,
                const uint64_t*seeds,int n,int sweeps,int nth,uint64_t*out,double*values){
 atomic<int>next{0};vector<thread>workers;
 for(int t=0;t<nth;t++)workers.emplace_back([&]{for(int i;(i=next++)<n;){
  uint64_t state=0x9e3779b97f4a7c15ULL+i,m=seeds[i];if(!eight->valid(m))abort();
  double best=eight->value(m,six,q1,q3,q0,q2);
  for(int pass=0;pass<sweeps;pass++){
   bool improved=false;int first=rng(state)%56;
   for(int j=0;j<56;j++){int e=(first+j)%56;uint64_t candidate=m^(1ULL<<e);if(!eight->valid(candidate))continue;
    double v=eight->value(candidate,six,q1,q3,q0,q2);if(v>best+1e-12){m=candidate;best=v;improved=true;}}
   if(!improved)break;
  }out[i]=m;values[i]=best;
 }});for(auto&t:workers)t.join();
}
// Count possible link graphs over a specified K4-free seven-vertex base.
uint64_t count_extensions8(uint64_t base){
 vector<pair<int,int>>pairs;int pairix[7][7];for(int a=0;a<7;a++)for(int b=a+1;b<7;b++){pairix[a][b]=pairix[b][a]=pairs.size();pairs.push_back({a,b});}
 vector<uint32_t>forb;for(int i=0;i<35;i++)if((base>>i)&1){auto e=oracle->t7[i];forb.push_back((1u<<pairix[e[0]][e[1]])|(1u<<pairix[e[0]][e[2]])|(1u<<pairix[e[1]][e[2]]));}
 uint64_t count=0;for(uint32_t m=0;m<(1u<<21);m++){bool ok=true;for(auto f:forb)if((m&f)==f){ok=false;break;}count+=ok;}return count;
}
}
