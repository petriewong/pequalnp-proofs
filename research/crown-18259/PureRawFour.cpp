#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using W=uint16_t;
using S=std::vector<W>;
std::array<std::vector<std::pair<W,W>>,16384> opts;
std::array<int,16384> pop;
int mx(int a,int b){return std::max(a,b);}
int tmin(S const &q){
 int out=q.size();
 for(auto a:q){
  int t=pop[a]-1;
  for(auto b:q)t+=(b&a)!=b;
  out=mx(out,t);
 }
 for(int i=0;i<(int)q.size();i++)for(int j=0;j<i;j++){
  auto a=q[i],b=q[j]; auto u=W(a|b);
  // The union's incidence graph has two components if disjoint, one otherwise.
  // Ancestor OR circuits for these two required masks must connect each component.
  int t=pop[u]-((a&b)?1:2);
  for(auto c:q)t+=((c&a)!=c && (c&b)!=c);
  out=mx(out,t);
 }
 return out;
}
std::string key(S const &v,int k){
 std::string out(1,char(k));
 for(W a:v){out.push_back(char(a&255));out.push_back(char(a>>8));}
 return out;
}
std::unordered_set<std::string> seen;
long long calls=0;
std::vector<std::array<W,3>> witness;
void insert(S &s,W y){if(y&&pop[y]>1){
 auto it=std::lower_bound(s.begin(),s.end(),y);
 if(it==s.end()||*it!=y)s.insert(it,y);
}}
void ensure(int);
bool solve(S const &s,int k){
 ++calls;
 if(s.empty())return true;
 if((int)s.size()>k||tmin(s)>k)return false;
 std::string memo=key(s,k);
 if(seen.count(memo))return false;
 auto j=std::max_element(s.begin(),s.end(),[](W a,W b){return std::make_pair(pop[a],a)<std::make_pair(pop[b],b);});
 W z=*j; ensure(z);
 S tail=s;tail.erase(tail.begin()+(j-s.begin()));
 for(auto [a,b]:opts[z]){
  S r=tail;insert(r,a);insert(r,b);
  if(solve(r,k-1)){witness.push_back({z,a,b});return true;}
 }
 if(seen.size()>2000000)seen.clear();
 seen.insert(std::move(memo));
 return false;
}
#include <functional>
using M=uint16_t;
std::vector<M> universe;
std::array<M,8> sides;
std::unordered_set<std::string> visited;
long long templates=0, gateChecks=0, odd=0;
int fixed[7]{};
std::vector<std::pair<M,M>> optsFor[7];
M rx[7],ry[7];
bool found=false;
std::function<void(int)> generate;
int codeIndex[7];
void build(int budget){
 ++templates;
 // For each original raw variable build an 8-column OR-demand incidence signature.
 std::array<int,14> orig{};
 for(int i=0;i<7;i++)for(auto s:{std::make_pair(rx[i],i),std::make_pair(ry[i],i+7)}){
  for(int j=0;j<8;j++)if((s.first&sides[j])==s.first){orig[s.second]|=1<<j;}
 }
 std::vector<int> sig(orig.begin(),orig.end());
 std::sort(sig.begin(),sig.end());sig.erase(std::unique(sig.begin(),sig.end()),sig.end());
 if(!sig[0]){++odd;return;} // Can't omit a raw in an exact monotone Crown.
 int k=budget-(14-int(sig.size()));
 std::array<M,8> axes{};
 for(int col=0;col<8;col++){
  for(int raw=0;raw<(int)sig.size();raw++)if(sig[raw]>>col&1)axes[col]|=1<<raw;
  if(!axes[col])return;
 }
 S require;
 for(auto a:axes)insert(require,a);
 if(tmin(require)>k)return;
 auto code=key(require,k);
 if(!visited.insert(code).second)return;
 ++gateChecks;
 if(gateChecks%100000==0)std::cout<<"solver progress "<<templates<<" gates checked "<<gateChecks<<" calls "<<calls<<std::endl;
 if(solve(require,k)){
  found=true;std::cout<<"FOUND templates "<<templates<<" gateChecks "<<gateChecks<<" upper "<<budget<<" merges "<<14-sig.size()<<std::endl;
  std::cout<<"reps ";for(int x:fixed)std::cout<<x<<" ";std::cout<<std::endl;
  std::cout<<"raw sig ";for(int x:orig)std::cout<<x<<" ";std::cout<<std::endl;
  std::cout<<"compressed ";for(int x:sig)std::cout<<x<<" ";std::cout<<std::endl;
  for(auto a:witness)std::cout<<a[0]<<" "<<a[1]<<" "<<a[2]<<std::endl;
 }
}
void ensure(int x){
 if(x<1||pop[x]<=1||!opts[x].empty())return;
 for(int a=(x-1)&x;a;a=(a-1)&x)
  for(int b=(x-1)&x;b;b=(b-1)&x)
   if(a<b && (a|b)==x)opts[x].push_back({a,b});
}
int main(int argc,char**argv){
 int budget=std::stoi(argv[2]);
 for(int i=0;i<16384;i++)pop[i]=__builtin_popcount(i);
 // Lazy-precompute masks of no more than the largest target; exact target upper 14.
 for(int x=1;x<16384;x++)if(pop[x]<=6)ensure(x);
 // Add union decompositions lazily through the demand ancestors using given masks.
 for(int j=0;j<8;j++)for(int x=0;x<16;x++)if((x>>(j/2)&1)==(j%2))sides[j]|=1<<x;
 for(int mask=0;mask<16;mask++)for(int bits=0;bits<16;bits++)if(!(mask&bits)){
  M cube=0;
  for(int x=0;x<16;x++)if((x&~mask)==bits)cube|=1<<x;
  universe.push_back(cube);
 }
 std::ifstream in(argv[1]);
 int index=0;
 while(in>>fixed[0]){
  for(int i=1;i<7;i++)in>>fixed[i];
  ++index;
  for(int i=0;i<7;i++){
   M other=0;
   for(int j=0;j<7;j++)if(j!=i)other|=1<<fixed[j];
   std::vector<M> pool;
   for(M shape:universe)if((shape&(1<<fixed[i]))&&!(shape&other))pool.push_back(shape);
   optsFor[i].clear();for(M x:pool)for(M y:pool)optsFor[i].push_back({x,y});
   codeIndex[i]=i;
  }
  std::sort(codeIndex,codeIndex+7,[](int x,int y){return optsFor[x].size()<optsFor[y].size();});
  generate=[&](int j){
   if(found)return;
   if(j==7){build(budget);return;}
   int pos=codeIndex[j];
   for(auto [a,b]:optsFor[pos]){
    bool good=true;
    for(int k=0;k<j&&good;k++){int q=codeIndex[k];if((a&ry[q])||(b&rx[q]))good=false;}
    if(!good)continue;
    rx[pos]=a;ry[pos]=b;
    generate(j+1);
    if(found)return;
   }
  };
  generate(0);
  std::cout<<"rep "<<index<<" templates "<<templates<<" gatechecks "<<gateChecks<<" calls "<<calls<<std::endl;
  if(found)break;
 }
 std::cout<<"finish reps "<<index<<" templates "<<templates<<" gatechecks "<<gateChecks<<" odd "<<odd<<" found "<<found<<std::endl;
}
