// Independent integer evaluator for selected five-root/six-vertex flag blocks.
// Included into the portable original ordered-root exhaustive verifier.
#include <climits>
#include <stdexcept>

struct FiveExact {
 struct Block { uint16_t sigma; uint32_t d; vector<uint32_t> flags; vector<int64_t> q; };
 struct Extension { uint64_t mask=0; array<uint16_t,1024> reorder{}; };
 struct RootSet { uint64_t mask=0; Extension a,b; };
 vector<Block> blocks;
 vector<RootSet> roots;
 array<int16_t,1024> block_at{};
 vector<array<int16_t,1024>> flag_at;
 vector<uint64_t> check_masks;
 static int64_t narrow(__int128 value) {
  if(value < LLONG_MIN || value > LLONG_MAX) throw runtime_error("five-root int64 overflow");
  return (int64_t)value;
 }
 template<class T> static T read(ifstream& f) {
  T value; f.read(reinterpret_cast<char*>(&value),sizeof(T));
  if(!f) throw runtime_error("truncated five-root candidate"); return value;
 }
 static uint32_t permute(uint32_t mask, const vector<array<int,3>>& t,
                          const vector<int>& p) {
  uint32_t out=0;
  for(size_t i=0;i<t.size();++i) if(mask&(1u<<i)) {
   auto e=t[i]; array<int,3> v={p[e[0]],p[e[1]],p[e[2]]}; sort(v.begin(),v.end());
   auto it=find(t.begin(),t.end(),v);
   if(it==t.end()) throw runtime_error("bad permutation");
   out |= 1u<<(it-t.begin());
  }
  return out;
 }
 static bool free6(uint32_t mask, const vector<array<int,3>>& t) {
  for(int a=0;a<6;++a) for(int b=a+1;b<6;++b)
   for(int c=b+1;c<6;++c) for(int d=c+1;d<6;++d) {
    array<int,4> four={a,b,c,d}; uint32_t forbidden=0;
    for(int omit=0;omit<4;++omit) {
     array<int,3> e{}; int z=0;
     for(int i=0;i<4;++i) if(i!=omit) e[z++]=four[i];
     forbidden |= 1u<<(find(t.begin(),t.end(),e)-t.begin());
    }
    if((mask&forbidden)==forbidden) return false;
   }
  return true;
 }
 explicit FiveExact(ifstream& input) {
  block_at.fill(-1); flag_at.resize(1024);
  for(auto& row:flag_at) row.fill(-1);
  uint32_t count=read<uint32_t>(input);
  if(count>23) throw runtime_error("too many five-root blocks");
  auto t5=triples(5),t6=triples(6),t7=triples(7);
  vector<pair<int,int>> pairs;
  for(int a=0;a<5;++a) for(int b=a+1;b<5;++b) pairs.push_back({a,b});
  array<uint32_t,1024> base{},extension{};
  for(int bits=0;bits<1024;++bits) {
   for(int bit=0;bit<10;++bit) if(bits&(1<<bit)) {
    base[bits] |= 1u<<(find(t6.begin(),t6.end(),t5[bit])-t6.begin());
    auto [a,b]=pairs[bit]; array<int,3> e={a,b,5};
    extension[bits] |= 1u<<(find(t6.begin(),t6.end(),e)-t6.begin());
   }
  }
  vector<vector<int>> perms; vector<int> p={0,1,2,3,4};
  do {perms.push_back(p);} while(next_permutation(p.begin(),p.end()));
  for(uint32_t bi=0;bi<count;++bi) {
   Block block; block.sigma=read<uint16_t>(input); block.d=read<uint32_t>(input);
   if(block.sigma>=1024 || block.d>1024 || !block.d) throw runtime_error("bad five-root block");
   for(const auto& previous:blocks) if(previous.sigma==block.sigma) throw runtime_error("duplicate type");
   uint32_t canonical=1024;
   for(const auto& perm:perms) canonical=min(canonical,permute(block.sigma,t5,perm));
   if(canonical!=block.sigma) throw runtime_error("noncanonical five-root type");
   block.flags.resize(block.d);
   for(auto& flag:block.flags) flag=read<uint32_t>(input);
   vector<uint32_t> independently_enumerated;
   for(int ext=0;ext<1024;++ext) {
    uint32_t flag=base[block.sigma]|extension[ext];
    if(free6(flag,t6)) independently_enumerated.push_back(flag);
   }
   sort(independently_enumerated.begin(),independently_enumerated.end());
   if(block.flags!=independently_enumerated) throw runtime_error("incomplete or misordered five-root flags");
   vector<int64_t> raw((size_t)block.d*block.d);
   for(auto& value:raw) value=read<int64_t>(input);
   for(size_t a=0;a<block.d;++a) for(size_t b=0;b<a;++b)
    if(raw[a*block.d+b]!=raw[b*block.d+a]) throw runtime_error("nonsymmetric Gram");
   block.q.assign(raw.size(),0);
   for(const auto& perm:perms) if(permute(block.sigma,t5,perm)==block.sigma) {
    vector<int> sixperm=perm; sixperm.push_back(5); vector<size_t> ids;
    for(uint32_t flag:block.flags) {
     uint32_t moved=permute(flag,t6,sixperm);
     auto it=lower_bound(block.flags.begin(),block.flags.end(),moved);
     if(it==block.flags.end() || *it!=moved) throw runtime_error("invalid flag automorphism");
     ids.push_back(it-block.flags.begin());
    }
    for(size_t a=0;a<block.d;++a) for(size_t b=0;b<block.d;++b)
     block.q[a*block.d+b]=narrow((__int128)block.q[a*block.d+b]+raw[ids[a]*block.d+ids[b]]);
   }
   for(int rooted=0;rooted<1024;++rooted) {
    for(const auto& perm:perms) if(permute(rooted,t5,perm)==block.sigma) {
     if(block_at[rooted]>=0) throw runtime_error("overlapping type classes");
     block_at[rooted]=bi; vector<int> sixperm=perm; sixperm.push_back(5);
     for(int ext=0;ext<1024;++ext) {
      uint32_t flag=permute(base[rooted]|extension[ext],t6,sixperm);
      auto it=lower_bound(block.flags.begin(),block.flags.end(),flag);
      if(it!=block.flags.end() && *it==flag) flag_at[rooted][ext]=it-block.flags.begin();
     }
     break;
    }
   }
   blocks.push_back(std::move(block));
  }
  uint32_t ncheck=read<uint32_t>(input);
  if(ncheck>100) throw runtime_error("excessive exact check masks");
  for(uint32_t i=0;i<ncheck;++i) {
   uint64_t mask=read<uint64_t>(input);
   if(mask>=(1ULL<<35)) throw runtime_error("invalid exact check mask");
   check_masks.push_back(mask);
  }
  if(input.peek()!=ifstream::traits_type::eof()) throw runtime_error("trailing candidate bytes");
  for(int u=0;u<7;++u) for(int v=u+1;v<7;++v) {
   vector<int> vertices; for(int w=0;w<7;++w) if(w!=u && w!=v) vertices.push_back(w);
   RootSet root;
   for(auto triple:t5) {
    array<int,3> e={vertices[triple[0]],vertices[triple[1]],vertices[triple[2]]};
    root.mask |= 1ULL<<(find(t7.begin(),t7.end(),e)-t7.begin());
   }
   auto build_extension=[&](int outside) {
    Extension emb; vector<pair<int,int>> reorder;
    for(int bit=0;bit<10;++bit) {
     auto [a,b]=pairs[bit]; array<int,3> e={vertices[a],vertices[b],outside};
     sort(e.begin(),e.end()); int global=find(t7.begin(),t7.end(),e)-t7.begin();
     emb.mask |= 1ULL<<global; reorder.push_back({global,bit});
    }
    sort(reorder.begin(),reorder.end());
    for(int value=0;value<1024;++value) for(int bit=0;bit<10;++bit)
     if(value&(1<<bit)) emb.reorder[value] |= 1u<<reorder[bit].second;
    return emb;
   };
   root.a=build_extension(u); root.b=build_extension(v); roots.push_back(root);
  }
 }
 __int128 value(uint64_t mask) const {
  __int128 total=0;
  if(blocks.empty()) return total;
  for(const auto& root:roots) {
   int rooted=_pext_u64(mask,root.mask),bi=block_at[rooted];
   if(bi<0) continue;
   int a=flag_at[rooted][root.a.reorder[_pext_u64(mask,root.a.mask)]];
   int b=flag_at[rooted][root.b.reorder[_pext_u64(mask,root.b.mask)]];
   if(a<0 || b<0) throw runtime_error("forbidden six-vertex flag during evaluation");
   const auto& block=blocks[bi]; total+=(__int128)2*block.q[(size_t)a*block.d+b];
  }
  return total;
 }
};
