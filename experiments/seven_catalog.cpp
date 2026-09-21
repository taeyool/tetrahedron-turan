// Complete seven-vertex catalogue: canonical deletion plus six-vertex automorphisms.
// This changes representation only; every raw admissible extension is covered.
#include "../search/optimization_oracle.cpp"
#include <unordered_set>
#include <chrono>
#include <string>

int main(int argc,char**argv){
 if(argc!=4){std::cerr<<"usage: seven_catalog representatives.u32 masks.u64 manifest.json\n";return 2;}
 auto started=std::chrono::steady_clock::now();
 std::vector<uint32_t> reps(964);std::ifstream input(argv[1],std::ios::binary);
 input.read(reinterpret_cast<char*>(reps.data()),reps.size()*4);
 if(!input||input.peek()!=EOF)return 3;
 Oracle o(reps.data(),964);auto ps=perms6();
 std::vector<int16_t> inverse_canon(1<<20,-1);
 std::vector<std::vector<int>> aut(964);
 std::vector<uint16_t> link_perm(size_t(720)*(1<<15));
 for(int k=0;k<720;k++){
  auto p=ps[k];std::array<int,6> inv{};for(int i=0;i<6;i++)inv[p[i]]=i;
  int ik=std::lower_bound(ps.begin(),ps.end(),inv)-ps.begin();
  int pairmap[15];for(int j=0;j<15;j++){auto [a,b]=o.pairs[j];pairmap[j]=o.pairix[p[a]][p[b]];}
  auto* lut=link_perm.data()+size_t(k)*(1<<15);lut[0]=0;
  for(int a=1;a<(1<<15);a++){int b=__builtin_ctz(a);lut[a]=lut[a&(a-1)]|(1u<<pairmap[b]);}
  for(int h=0;h<964;h++){
   uint32_t z=0;for(int j=0;j<20;j++)if((reps[h]>>j)&1){auto e=o.t6[j];std::array<int,3> q={p[e[0]],p[e[1]],p[e[2]]};std::sort(q.begin(),q.end());z|=1u<<o.ix6[q[0]][q[1]][q[2]];}
   inverse_canon[z]=ik;if(z==reps[h])aut[h].push_back(k);
  }
 }
 auto min_link=[&](int h,int link){uint16_t best=link;for(int k:aut[h])best=std::min(best,link_perm[size_t(k)*(1<<15)+link]);return best;};
 auto canonical=[&](uint64_t m){
  uint64_t best=UINT64_MAX;
  for(int del=0;del<7;del++){
   int vs[6],n=0;for(int v=0;v<7;v++)if(v!=del)vs[n++]=v;
   uint32_t base=0;for(int j=0;j<20;j++){auto e=o.t6[j];if((m>>o.ix7[vs[e[0]]][vs[e[1]]][vs[e[2]]])&1)base|=1u<<j;}
   int h=o.canon[base];if(h<0)throw std::runtime_error("nonadmissible deletion");
   if((uint64_t(h)<<15)>best)continue;
   uint16_t link=0;for(int j=0;j<15;j++){auto [a,b]=o.pairs[j];std::array<int,3> e={vs[a],vs[b],del};std::sort(e.begin(),e.end());if((m>>o.ix7[e[0]][e[1]][e[2]])&1)link|=1u<<j;}
   int k=inverse_canon[base];if(k<0)throw std::runtime_error("missing canonical permutation");
   link=link_perm[size_t(k)*(1<<15)+link];
   best=std::min(best,(uint64_t(h)<<15)|min_link(h,link));
  }return best;
 };
 std::unordered_set<uint64_t> keys;uint64_t raw=0,base_orbits=0;
 for(int h=0;h<964;h++){
  for(int am:o.links[h]){
   raw++;if(min_link(h,am)!=am)continue;base_orbits++;
   uint64_t m=o.base7[h]|o.ext7[am];keys.insert(canonical(m));
  }
  if(h%50==0)std::cout<<"base="<<h<<" raw="<<raw<<" unique="<<keys.size()<<std::endl;
 }
 if(raw!=13051375)return 4;
 std::vector<uint64_t> ordered(keys.begin(),keys.end());std::sort(ordered.begin(),ordered.end());
 std::vector<uint64_t> masks;for(auto key:ordered)masks.push_back(o.base7[key>>15]|o.ext7[key&32767]);
 // Check canonical invariance under independently permuted vertex labels.
 uint64_t checked=0;std::array<int,7> perm={0,1,2,3,4,5,6};
 for(size_t i=0;i<masks.size();i+=std::max<size_t>(1,masks.size()/100)){
  auto target=canonical(masks[i]);perm={0,1,2,3,4,5,6};int count=0;
  do {uint64_t moved=0;for(int j=0;j<35;j++)if((masks[i]>>j)&1){auto e=o.t7[j];std::array<int,3> q={perm[e[0]],perm[e[1]],perm[e[2]]};std::sort(q.begin(),q.end());moved|=1ULL<<o.ix7[q[0]][q[1]][q[2]];}
      if(canonical(moved)!=target)return 5;checked++;count++;
  }while(std::next_permutation(perm.begin(),perm.end()));
 }
 std::ofstream output(argv[2],std::ios::binary);output.write(reinterpret_cast<char*>(masks.data()),masks.size()*8);output.close();if(!output)return 6;
 double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
 std::ofstream manifest(argv[3]);manifest<<"{\"status\":\"passed\",\"raw_extensions\":"<<raw<<",\"base_automorphism_orbits\":"<<base_orbits<<",\"seven_vertex_classes\":"<<masks.size()<<",\"permuted_label_checks\":"<<checked<<",\"seconds\":"<<seconds<<"}\n";
 std::cout<<"complete raw="<<raw<<" classes="<<masks.size()<<" seconds="<<seconds<<std::endl;
}
