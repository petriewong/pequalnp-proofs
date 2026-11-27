#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
using U=uint64_t;
U v[18], neg, pos;
int k, at, limit;
uint64_t layouts=0, candidates=0, interesting=0, pruneCuts=0, maxSavings=0;
int gateA[6], gateB[6], gateOr[6];
array<unsigned,256> options{};
bool canCover(const unsigned *o,int n,unsigned need,int budget) {
 if(!need)return true;
 if(!budget)return false;
 int gain=0, rare=10000; unsigned bit=0;
 for(int i=0;i<n;i++)gain=max(gain,__builtin_popcount(o[i]&need));
 if(gain*budget<__builtin_popcount(need))return false;
 for(unsigned pending=need;pending;pending&=pending-1){
   unsigned b=pending&-pending;int count=0;
   for(int i=0;i<n;i++)count+=!!(b&o[i]);if(!count)return false;
   if(count<rare){rare=count;bit=b;if(count==1)break;}
 }
 for(int i=0;i<n;i++)if((bit&o[i])&&canCover(o,n,need&~o[i],budget-1))return true;
 return false;
}
bool leaf(){
 layouts++;
 int n=0, saving=0;
 // Raw-raw pairs contribute at most one edge, so only examine pairs
 // involving a routing wire for the savings upper bound.
 for(int y=11;y<11+k;y++)for(int x=0;x<y;x++){
   U q=v[x]&v[y]; if((q&neg)||__builtin_popcountll(q)<2)continue;
   unsigned m=q&pos; if(find(options.begin(),options.begin()+n,m)!=options.begin()+n)continue;
   options[n++]=m; saving+=__builtin_popcount(m)-1;
 }
 maxSavings=max(maxSavings,uint64_t(saving));
 if(saving<16-limit){pruneCuts++;return false;}
 interesting++;
 // Add every allowed single-edge pair, a relaxation if identical
 // semantic signals or unused routing gates would be prohibited.
 for(int b=0;b<16;b++)options[n++]=1U<<b;
 if(!canCover(options.data(),n,unsigned(pos),limit))return false;
 cout<<"candidate (still verify output synthesis):\n";
 for(int j=0;j<k;j++)cout<<gateA[j]<<" "<<gateB[j]<<" "<<gateOr[j]<<"\n";
 return true;
}
bool dfs(int i,int ands){
 if(i==k)return leaf();
 bool allowAnd=ands<2, allowOr=k-i>2-ands;
 for(int y=1;y<11+i;y++)for(int x=0;x<y;x++){
   for(int o=0;o<2;o++){
     if(o?!allowOr:!allowAnd)continue;
     U z=o?v[x]|v[y]:v[x]&v[y];
     if(!o && !(z&neg)) continue;
     // Merging an equal wire on all complete decisive rows is safe.
     // Keep duplicates to preserve literal exact route counts.
     gateA[i]=x;gateB[i]=y;gateOr[i]=o;v[11+i]=z;
     if(dfs(i+1,ands+!o))return true;
   }
 }
 return false;
}
// Independently reconstruct all decisive rows, without oracle.txt.
static const pair<int,int> edges[16]={{0,9},{0,10},{1,4},{1,8},{2,5},{2,10},{3,6},{3,7},
 {4,8},{4,10},{5,8},{5,9},{6,7},{6,10},{7,9},{8,9}};
bool positive(int x){
 for(auto [a,b]:edges)if((x&(1<<a))&&(x&(1<<b)))return true;
 return false;
}
int main(int argc,char**argv){
 limit=atoi(argv[1]); k=22-2*limit;
 if(k<2 || k>4)return 2;
 vector<int> rows; for(auto [a,b]:edges)rows.push_back((1<<a)|(1<<b));
 for(int r=0;r<2048;r++){
   if(positive(r))continue;
   bool maximal=true;
   for(int j=0;j<11;j++)if(!(r&(1<<j))&&!positive(r|(1<<j)))maximal=false;
   if(maximal)rows.push_back(r);
 }
 int P=16,N=rows.size();
 assert(N==40);
 for(int j=0;j<11;j++)for(int t=0;t<N;t++)if(rows[t]&(1<<j))v[j]|=U(1)<<t;
 pos=(U(1)<<P)-1;neg=((U(1)<<N)-1)^pos;
 auto t=chrono::steady_clock::now();
 bool found=dfs(0,0);
 cout<<"terms "<<limit<<" layouts "<<layouts<<" by_saving "<<pruneCuts
     <<" by_exact_cover "<<interesting<<" upper_savings "<<maxSavings
     <<" result "<<(found?"candidate":"no cover")
     <<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t).count()<<"\n";
 return 0;
}
