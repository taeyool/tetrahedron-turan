"""Port the original ordered-root oracle without changing its arithmetic."""


def portable_ordered_source(source):
    replacements={
        "#include <immintrin.h>":"#include <thread>",
        "#include <omp.h>":"",
        "static inline int flagid":"static inline uint64_t _pext_u64(uint64_t v,uint64_t m){uint64_t out=0,b=1;while(m){uint64_t z=m&-m;if(v&z)out|=b;m&=m-1;b<<=1;}return out;}\nstatic inline int flagid",
        "if(nth>0)omp_set_num_threads(nth);":"if(nth<1)return 2;",
        "vector<ThreadBest> best(omp_get_max_threads());":"vector<ThreadBest> best(nth);",
        "#pragma omp parallel for schedule(dynamic,1)\n for(long long si=0;si<(long long)Sids.size();si++){\n  int tid=omp_get_thread_num()":"vector<thread> workers;for(int worker=0;worker<nth;worker++)workers.emplace_back([&,worker]{for(long long si=worker;si<(long long)Sids.size();si+=nth){int tid=worker",
        "\n ThreadBest ans;":"\n });for(auto&worker:workers)worker.join();\n ThreadBest ans;",
    }
    for old,new in replacements.items():
        assert source.count(old)==1,old
        source=source.replace(old,new)
    return source
