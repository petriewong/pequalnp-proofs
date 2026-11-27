#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
using W=uint32_t;
constexpr int Q=21,U=1<<Q,G=63;
constexpr std::array<int,Q> rows{84,98,140,161,266,273,63,79,121,151,186,219,295,316,365,438,455,457,466,484,504};
struct Tables{
 std::vector<std::vector<W>> levels;
 std::vector<uint8_t> cost;
 Tables(int max):levels(max+1),cost(U,255){
  for(int i=0;i<9;i++){
   W z=0;for(int j=0;j<Q;j++)z|=((rows[j]>>i)&1)<<j;
   levels[0].push_back(z);cost[z]=0;
  }
  for(int k=1;k<=max;k++){
   auto add=[&](W z){if(cost[z]==255){cost[z]=k;levels[k].push_back(z);}};
   for(int a=0;a<k-a;a++){
    int b=k-a-1;
    for(W x:levels[a])for(W y:levels[b])if(a!=b||x<y){add(x|y);add(x&y);}
   }
  }
 }
};
std::vector<std::array<int,Q>> actions(){
 std::vector<std::array<int,Q>> out;
 std::array<int,3> a{0,1,2};
 do{
  std::array<int,3> b{0,1,2};
  do{
   for(bool t:{false,true}){
    std::array<int,Q> act{};
    for(int j=0;j<Q;j++){
     int p=0;
     for(int x=0;x<9;x++)if(rows[j]>>x&1){
      int r=x/3,c=x%3;if(t)std::swap(r,c);
      p|=1<<(3*a[r]+b[c]);
     }
     auto it=std::find(rows.begin(),rows.end(),p);
     if(it==rows.end())throw std::runtime_error("orbit action");
     act[j]=it-rows.begin();
    }
    out.push_back(act);
   }
  }while(std::next_permutation(b.begin(),b.end()));
 }while(std::next_permutation(a.begin(),a.end()));
 return out;
}
int main(int argc,char **argv){
 if(argc<3)return 2;
 int n=std::stoi(argv[2]);
 if(n<0||n>13)return 2;
 Tables pure(n);
 std::string op=argv[1];
 if(op=="orbits"){
  auto perm=actions();
  std::vector<bool> seen(U,false);
  int cnt=0;
  for(W w:pure.levels[n]){
   if(seen[w])continue;
   ++cnt;
   W rep=w;
   for(auto const &p:perm){
    W v=0;
    for(W u=w;u;u&=u-1)v|=1u<<p[__builtin_ctz(u)];
    if(pure.cost[v]!=n)throw std::runtime_error("cost symmetry");
    seen[v]=true;rep=std::min(rep,v);
   }
   std::cout<<rep<<"\n";
  }
  std::cerr<<"orbits cost "<<n<<" signatures "<<pure.levels[n].size()<<" representatives "<<cnt<<"\n";
  return 0;
 }
 if(op!="run"||argc!=6)return 2;
 std::ifstream f(argv[3]);if(!f)return 3;
 int shard=std::stoi(argv[4]),parts=std::stoi(argv[5]);
 if(parts<1||shard<0||shard>=parts)return 2;
 std::vector<uint8_t> imp(U,255);
 std::vector<std::vector<W>> lev(n+1);
 W m; int idx=0,tested=0;
 while(f>>m){
  if(idx++%parts!=shard)continue;
  if(m>=U)return 4;
  ++tested;
  auto hit=[&](int k,W z){
   if(pure.cost[z]>k&&imp[z]==255){imp[z]=k;lev[k].push_back(z);}
  };
  hit(0,m);
  for(int k=1;k<=n;k++){
   for(int a=0;a<k;a++){
    int b=k-1-a;
    for(W x:lev[a]){
     for(W y:pure.levels[b]){hit(k,x&y);hit(k,x|y);}
     if(a<=b)for(W y:lev[b])if(a!=b||x<y){hit(k,x&y);hit(k,x|y);}
    }
   }
   if(imp[G]!=255){
    std::cout<<"FOUND "<<m<<" with residual "<<int(imp[G])<<"\n";return 0;
   }
  }
  for(auto &l:lev){for(W x:l)imp[x]=255;l.clear();}
  if(tested%250==0)std::cout<<"checked "<<tested<<std::endl;
 }
 std::cout<<"complete residual "<<n<<" shard "<<shard<<"/"<<parts<<" macros "<<tested<<", no witness\n";
}
