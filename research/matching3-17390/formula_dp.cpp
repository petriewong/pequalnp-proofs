#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

// Signatures on six minimal positive and fifteen maximal negative assignments.
// Every monotone formula correct on these antichains is correct on all 512 rows.
int main(int argc,char **argv) {
 constexpr int wanted=(1<<6)-1, universe=1<<21;
 constexpr int rows[]={84,98,140,161,266,273,63,79,121,151,186,219,295,316,365,438,455,457,466,484,504};
 int cap=argc>1?std::atoi(argv[1]):13;
 if(cap<0||cap>25)return 2;
 std::vector<uint8_t> d(universe,255);
 std::vector<std::vector<uint32_t>> level(cap+1);
 for(int i=0;i<9;i++){
  uint32_t z=0;
  for(int j=0;j<21;j++)z|=((rows[j]>>i)&1)<<j;
  d[z]=0;level[0].push_back(z);
 }
 for(int k=1;k<=cap;k++){
  auto record=[&](uint32_t z){
   if(d[z]==255){d[z]=k;level[k].push_back(z);}
  };
  for(int a=0;a<k-a;a++){
   int b=k-a-1;
   auto const &A=level[a];auto const &B=level[b];
   for(uint32_t i:A)for(uint32_t j:B){
    if(a==b&&i>=j)continue;
    record(i&j);record(i|j);
   }
  }
  std::cout<<"complete formula cost "<<k<<": "<<level[k].size()<<" new signatures"<<std::endl;
  if(d[wanted]!=255){std::cout<<"first target cost "<<int(d[wanted])<<std::endl;return 0;}
 }
 std::cout<<"no formula through cost "<<cap<<std::endl;
}
