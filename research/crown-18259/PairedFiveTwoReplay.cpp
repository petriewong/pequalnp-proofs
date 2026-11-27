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
std::array<std::vector<std::pair<W,W>>,512> opts;
std::array<int,512> pop;
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
bool solve(S const &s,int k){
 ++calls;
 if(s.empty())return true;
 if((int)s.size()>k||tmin(s)>k)return false;
 std::string memo=key(s,k);
 if(seen.count(memo))return false;
 auto j=std::max_element(s.begin(),s.end(),[](W a,W b){return std::make_pair(pop[a],a)<std::make_pair(pop[b],b);});
 W z=*j;
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
struct Cut { W a,b; uint32_t cover; int cost; };
constexpr W H1=128,H2=256,C=127;
int nonRawPairs(S const &s) {
 int k=0;
 for (W a:s) k += ((a&(H1|H2))!=0 || pop[a]!=2);
 return k;
}
constexpr uint32_t Goal=(1<<21)-1;
std::array<uint32_t,128> hits;
std::unordered_set<std::string> checked;
long long shapes=0,cleanShapes=0,passed=0,gateChecks=0;
int budget=8; int shard=0,shards=1;
bool checkPair(W A,W B,W U,W V){
 if((U<128&&pop[U]==1)||(V<128&&pop[V]==1))return false;
 ++shapes;
 W d1=A&B;
 auto h1=hits[A]&hits[B];
 W ua=(U&C)|((U&H1)?d1:0), vb=(V&C)|((V&H1)?d1:0);
 uint32_t up=hits[U&C]|((U&H1)?h1:0), vp=hits[V&C]|((V&H1)?h1:0);
 W d2=ua&vb;uint32_t h2=up&vp;
 if(((ua&vb)==ua&&(up&vp)==up)||((ua&vb)==vb&&(up&vp)==vp))return false;
 if(!d2 || (d1==d2 && h1==h2)) return false;
 S basis; for(W s:{A,B,U,V})insert(basis,s);
 if(tmin(basis)>budget)return false;
 if((int)basis.size()>=budget)return false;
 if(budget==8&&nonRawPairs(basis)>2)return false;
 ++cleanShapes;
 std::array<W,512> diag;
 std::array<uint32_t,512> pos;
 for(W x=1;x<512;x++){
  diag[x]=(x&C)|((x&H1)?d1:0)|((x&H2)?d2:0);
  pos[x]=hits[x&C]|((x&H1)?h1:0)|((x&H2)?h2:0);
 }
 std::vector<Cut> terms;
 for(W a=1;a<512;a++){
  if(a<128&&pop[a]==1)continue;
  W free=C^diag[a];
  for(int placement=0;placement<4;placement++){
   W hs=W(placement<<7);
   if((placement&1)&&(d1&diag[a]))continue;
   if((placement&2)&&(d2&diag[a]))continue;
   for(W br=free;;br=(br-1)&free){
    W b=hs|br;
    if(b>a && !(b<128&&pop[b]==1)){
     uint32_t v=pos[a]&pos[b];
     if(v){S q=basis;insert(q,a);insert(q,b);if((budget!=8||nonRawPairs(q)<=2)&&tmin(q)<=budget)terms.push_back({a,b,v,int(q.size()-basis.size())});}
    }
    if(!br)break;
   }
  }
 }
 int spare=budget-basis.size();
 std::array<int,22> bestPerSize{};
 bestPerSize.fill(-1);
 for(auto c:terms)bestPerSize[__builtin_popcount(c.cover)]=std::max(bestPerSize[__builtin_popcount(c.cover)],2-c.cost);
 for(int i=20;i>=0;i--)bestPerSize[i]=std::max(bestPerSize[i],bestPerSize[i+1]);
 std::sort(terms.begin(),terms.end(),[](Cut a,Cut b){return __builtin_popcount(a.cover)>__builtin_popcount(b.cover);});
 std::array<std::vector<int>,21> table;
 for(int j=0;j<(int)terms.size();j++)for(int k=0;k<21;k++)if(terms[j].cover>>k&1)table[k].push_back(j);
 std::unordered_map<uint32_t,std::vector<int>> viable;
 for(int i=0;i<(int)terms.size()&&__builtin_popcount(terms[i].cover)>=7;i++){
  auto a=terms[i];
  auto clash=[](Cut a,Cut b){return a.a==b.a||a.a==b.b||a.b==b.a||a.b==b.b;};
  for(int j=i+1;j<(int)terms.size();j++){
   auto b=terms[j];
   if(__builtin_popcount(a.cover)+2*__builtin_popcount(b.cover)<21)break;
   if(a.cost+b.cost>spare || clash(a,b))continue;
   if(a.cost+b.cost+2-bestPerSize[1]>spare)continue;
   auto need=Goal&~(a.cover|b.cover);
   if(!need)continue;
   int req=__builtin_popcount(need);
   if(__builtin_popcount(b.cover)<req)continue;
   if(a.cost+b.cost+2-bestPerSize[req]>spare)continue;
   int k=__builtin_ctz(need);
   for(uint32_t m=need;m;m&=m-1){int g=__builtin_ctz(m);if(table[g].size()<table[k].size())k=g;}
   S p=basis;for(W x:{a.a,a.b,b.a,b.b})insert(p,x);
   if((budget==8&&nonRawPairs(p)>2)||tmin(p)>budget)continue;
   auto it=viable.find(need);
   if(it==viable.end()){
    std::vector<int> hit;
    for(int jj:table[k]){
     if(__builtin_popcount(terms[jj].cover)<req)break;
     if((terms[jj].cover&need)==need)hit.push_back(jj);
    }
    it=viable.emplace(need,std::move(hit)).first;
   }
   for(int jj:it->second){
    if(jj<=j)continue;
    auto c=terms[jj];
    if(a.cost+b.cost+c.cost>spare || clash(a,c)||clash(b,c))continue;
    W needHelper=a.a|a.b|b.a|b.b|c.a|c.b;
    if(!(needHelper&H2) || !((needHelper|U|V)&H1))continue;
    ++passed;
    S q=p;insert(q,c.a);insert(q,c.b);
    if((budget==8&&nonRawPairs(q)>2)||tmin(q)>budget)continue;
    if(!checked.insert(key(q,budget)).second)continue;
    ++gateChecks;
    if(!solve(q,budget))continue;
    std::cout<<"FOUND "<<A<<" "<<B<<" "<<U<<" "<<V<<" -> "<<a.a<<" "<<a.b<<" "<<b.a<<" "<<b.b<<" "<<c.a<<" "<<c.b<<std::endl;
    for(auto o:witness)std::cout<<o[0]<<" "<<o[1]<<" "<<o[2]<<std::endl;
    return true;
   }
  }
 }
 return false;
}
int main(int argc,char**argv){
 if(argc>1)budget=std::stoi(argv[1]);
 if(argc>2)shard=std::stoi(argv[2]);
 if(argc>3)shards=std::stoi(argv[3]);
 for(int i=0;i<512;i++)pop[i]=__builtin_popcount(i);
 for(int x=1;x<512;x++){
  if(pop[x]<2)continue;
  for(int a=(x-1)&x;a;a=(a-1)&x)
   for(int b=(x-1)&x;b;b=(b-1)&x)
    if(a<b&&(a|b)==x)opts[x].push_back({a,b});
 }
 for(int x=0;x<128;x++)for(int i=0,k=0;i<7;i++)for(int j=i+1;j<7;j++,k++)
  if(x&((1<<i)|(1<<j)))hits[x]|=1<<k;
 int shape=0;
 for(int a=1;a<7;a++)for(int b=a;b<=7-a;b++)for(int c=1;c<=7-a-b;c++){
  if(shape++%shards!=shard)continue;
  W d1=W(((1<<c)-1)<<(a+b));
  W A=W(((1<<a)-1)|d1),B=W((((1<<b)-1)<<a)|d1);
  int p[7];
  for(int i=0;i<7;i++)p[i]=i<a?1:i<a+b?2:i<a+b+c?3:0;
  std::function<bool(int,int,W,W)> go=[&](int i,int l,W U,W V)->bool {
   if(i==7){
    for(int placement=0;placement<4;placement++){
     W x=U|((placement&1)?H1:0),y=V|((placement&2)?H1:0);
     if(x&&y&&checkPair(A,B,x,y))return true;
    }
    return false;
   }
   int min=i>0&&p[i-1]==p[i]?l:0;
   for(int q=min;q<4;q++)
    if(go(i+1,q,W(U|((q&1)?1<<i:0)),W(V|((q&2)?1<<i:0))))return true;
   return false;
  };
  if(go(0,0,0,0))return 0;
  std::cout<<"shape "<<a<<","<<b<<","<<c<<" helpers "<<shapes<<" clean "<<cleanShapes<<" term pairs "<<passed<<" tests "<<gateChecks<<" dp calls "<<calls<<std::endl;
 }
 std::cout<<"complete paired5 two dirty, budget "<<budget<<" shard "<<shard<<"/"<<shards<<", helpers "<<shapes<<" pairs "<<passed<<" tested "<<gateChecks<<std::endl;
}
