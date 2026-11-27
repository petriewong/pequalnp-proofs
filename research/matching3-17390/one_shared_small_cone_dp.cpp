#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <array>
#include <functional>
#include <vector>

// Signatures on six minimal positive and fifteen maximal negative assignments.
// Every monotone formula correct on these antichains is correct on all 512 rows.
int main(int argc,char **argv) {
 constexpr int wanted=(1<<6)-1, universe=1<<21;
 constexpr int rows[]={84,98,140,161,266,273,63,79,121,151,186,219,295,316,365,438,455,457,466,484,504};
 int mode=argc>1?std::atoi(argv[1]):0;
 int shape=argc>2?std::atoi(argv[2]):0;
 int cap=argc>3?std::atoi(argv[3]):12;
 if(mode<0||mode>1||shape<0||shape>1)return 2;
 int other=shape?4:1;
 bool triple=argc==6;
 int hi=triple?std::atoi(argv[4]):0;
 int third=triple?std::atoi(argv[5]):0;
 if(triple&&(hi<0||hi>1||third<=0||third>=9||third==other))return 2;
 if(cap<0||cap>25)return 2;
 struct Node {uint32_t a=0,b=0; int code=0;};
 std::vector<Node> recipe(universe);
 std::vector<uint8_t> d(universe,255);
 std::array<uint32_t,9> raw{};
 std::vector<std::vector<uint32_t>> level(cap+1);
 for(int i=0;i<9;i++){
  uint32_t z=0;
  for(int j=0;j<21;j++)z|=((rows[j]>>i)&1)<<j;
  raw[i]=z;d[z]=0;level[0].push_back(z);recipe[z].code=i;
 }
 auto macro=mode?(raw[0]|raw[other]):(raw[0]&raw[other]);
 if(triple)macro=hi?(macro|raw[third]):(macro&raw[third]);
 if(d[macro]==0)return 3;
 d[macro]=0;level[0].push_back(macro);recipe[macro].code=triple?10:9;
 std::cout<<"raw macro "<<mode<<" "<<shape<<" triple "<<triple<<" "<<hi<<" "<<third<<std::endl;
 for(int k=1;k<=cap;k++){
  auto record=[&](uint32_t z,uint32_t a,uint32_t b,int op){
   if(d[z]==255){d[z]=k;level[k].push_back(z);recipe[z]={a,b,op};}
  };
  for(int a=0;a<k-a;a++){
   int b=k-a-1;
   auto const &A=level[a];auto const &B=level[b];
   for(uint32_t i:A)for(uint32_t j:B){
    if(a==b&&i>=j)continue;
    record(i&j,i,j,0);record(i|j,i,j,1);
   }
  }
  std::cout<<"complete formula cost "<<k<<": "<<level[k].size()<<" new signatures"<<std::endl;
  if(d[wanted]!=255){
   std::cout<<"first target cost "<<int(d[wanted])<<" plus macro"<<std::endl;
   std::cout<<"gate "<<mode<<" 0 "<<other<<std::endl;
   if(triple)std::cout<<"gate "<<hi<<" 9 "<<third<<std::endl;
   int idx=triple?11:10;
   std::function<int(uint32_t)> emit=[&](uint32_t z){
    auto q=recipe[z];
    if(d[z]==0)return q.code;
    int a=emit(q.a),b=emit(q.b);
    std::cout<<"gate "<<q.code<<" "<<a<<" "<<b<<std::endl;
    return idx++;
   };
   emit(wanted);
   return 0;
  }
 }
 std::cout<<"no formula through cost "<<cap<<std::endl;
}
