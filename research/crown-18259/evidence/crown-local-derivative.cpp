#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using M=uint64_t;
constexpr int N=14;
struct G {int op,a,b;};
using C=std::vector<G>;
std::array<M,N> raw;
M goal=0,all=(1ull<<49)-1;
long long tests=0;
M comb(G g, M a, M b){return g.op?a|b:a&b;}
int cost(M v){return __builtin_popcountll(v^goal);}
M run(C const& c,int force=-1,M forced=0,std::array<M,64>* vals=nullptr){
 std::array<M,64> w{};
 std::copy(raw.begin(),raw.end(),w.begin());
 for(int j=0;j<(int)c.size();j++){
  auto g=c[j];
  if(g.a>=N+j||g.b>=N+j||g.a<0||g.b<0)throw std::runtime_error("forward pointer");
  w[N+j]=j==force?forced:comb(g,w[g.a],w[g.b]);
 }
 if(vals)*vals=w;
 return w[N+c.size()-1];
}
C prune(C const& c,int dead,int replace){
 C out;
 auto m=[&](int x){return x==N+dead?replace:x-(x>N+dead);};
 for(int i=0;i<(int)c.size();i++)if(i!=dead){auto g=c[i];out.push_back({g.op,m(g.a),m(g.b)});}
 return out;
}
bool emit(C const& c){
 if(run(c)!=goal)throw std::runtime_error("false candidate");
 std::cout<<"FOUND 22\n";
 for(auto g:c)std::cout<<g.op<<" "<<g.a<<" "<<g.b<<"\n";
 return true;
}
int bestone(C& c,int at,std::mt19937_64& rng,bool verify){
 std::array<M,64> w; auto original=run(c,-1,0,&w);
 auto q0=run(c,at,0),q1=run(c,at,all);
 int best=cost(original), ties=1;
 G chosen=c[at];
 for(int a=0;a<N+at;a++)for(int b=a;b<N+at;b++)for(int o:{0,1}){
  G g{o,a,b};
  M with=q0|(comb(g,w[a],w[b])&q1);
  int d=cost(with); ++tests;
  if(d<best){best=d;chosen=g;ties=1;}
  else if(d==best){if(rng()%++ties==0)chosen=g;}
  if(best==0){c[at]=chosen; if(run(c)!=goal)throw std::runtime_error("bad candidate"); return 0;}
 }
 c[at]=chosen;
 if(verify&&cost(run(c))!=best)throw std::runtime_error("Boolean derivative mismatch");
 return best;
}
int main(int argc,char**argv){
 if(argc!=4)return 2;
 for(int i=0;i<7;i++)for(int j=0;j<7;j++){
  auto b=1ull<<(7*i+j);raw[i]|=b;raw[7+j]|=b;if(i!=j)goal|=b;
 }
 std::ifstream f(argv[1]);
 int n,count=0,best=49;
 std::mt19937_64 rng(std::stoull(argv[2]));
 std::vector<std::pair<int,C>> starters;
 while(f>>n){
  ++count;C base(n);
  for(auto& g:base)f>>g.op>>g.a>>g.b;
  if(run(base)!=goal||n!=23)throw std::runtime_error("bad control");
  for(int d=0;d<n-1;d++)for(int k=0;k<N+d;k++){
   C c=prune(base,d,k);int val=cost(run(c));
   if(!val){emit(c);return 0;}
   C improved=c;
   for(int j=0;j<(int)c.size();j++){
    C v=c;int val2=bestone(v,j,rng,true);
    if(!val2){emit(v);return 0;}
    if(val2<val){improved=std::move(v);val=val2;}
   }
   best=std::min(best,val);starters.emplace_back(val,std::move(improved));
  }
 }
 std::sort(starters.begin(),starters.end(),[](auto const&a,auto const&b){return a.first<b.first;});
 std::cout<<"complete single replacements "<<count<<" controls "<<starters.size()<<" deletions "<<tests<<" trials; nearest "<<best<<std::endl;
 long long near=0,before=tests;
 for(auto const& entry:starters){
  if(entry.first!=1)break;
  ++near;
  for(int j=0;j<(int)entry.second.size();j++){
   C c=entry.second;
   if(!bestone(c,j,rng,true)){emit(c);return 0;}
  }
 }
 std::cout<<"complete one extra replacement from "<<near<<" selected distance-one states, "<<tests-before<<" trials"<<std::endl;
 int sec=std::atoi(argv[3]);long long runs=0, sweeps=0;
 auto t=std::chrono::steady_clock::now();
 while(std::chrono::steady_clock::now()-t<std::chrono::seconds(sec)){
  ++runs;
  int stop=runs%5?std::min<int>(starters.size(),80):starters.size();
  C c=starters[rng()%stop].second;
  for(int tries=0;tries<30;tries++){
   if(tries==0||tries%7==0){
    for(int f=0;f<(tries==0?2:1);f++){
     int j=rng()%c.size();c[j]={int(rng()%2),int(rng()%(N+j)),int(rng()%(N+j))};
    }
    if(run(c)==goal){emit(c);return 0;}
   }
   auto j=rng()%c.size();int cur=bestone(c,j,rng,false);++sweeps;
   if(!cur){emit(c);return 0;}
   best=std::min(best,cur);
  }
 }
 std::cout<<"complete heuristic "<<runs<<" restarts "<<sweeps<<" optimizations "<<tests<<" trials total, nearest "<<best<<std::endl;
}
