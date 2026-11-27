#include <array>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
struct G{int a,b,o;};
struct T{unsigned m;int a,b;};
uint64_t z0[26], pos, neg;
int k, nterms, best=999;
mt19937 rng;
vector<T> chosen;
bool cover(const vector<T>& opt,unsigned missing,int slots,vector<T>& path){
 if(!missing)return true;
 if(!slots)return false;
 unsigned mw=0;int rare=999;
 for(unsigned x=missing;x;x&=x-1){
  unsigned bit=x&-x;int c=0;
  for(auto &t:opt)c+=!!(t.m&bit);
  if(c<rare){rare=c;mw=bit;if(c<2)break;}
 }
 int mxgain=0;
 for(auto &t:opt)mxgain=max(mxgain,__builtin_popcount(t.m&missing));
 if(!rare||slots*mxgain<__builtin_popcount(missing))return false;
 for(auto &t:opt)if(t.m&mw){
  path.push_back(t);
  if(cover(opt,missing&~t.m,slots-1,path))return true;
  path.pop_back();
 }
 return false;
}
int run(const vector<G>& gates){
 uint64_t z[26];copy(z0,z0+11,z);
 int bad=0;
 for(int j=0;j<k;j++){
  auto g=gates[j];z[11+j]=g.o?z[g.a]|z[g.b]:z[g.a]&z[g.b];
  if(!g.o && (z[11+j]&neg)==0)bad++;
 }
 vector<T> options;unsigned all=0;
 for(int a=0;a<11+k;a++)for(int b=a+1;b<11+k;b++){
  uint64_t v=z[a]&z[b];if(!v || (v&neg))continue;
  unsigned m=v&pos;all|=m;
  options.push_back({m,a,b});
 }
 int gone=__builtin_popcount(unsigned(pos)&~all);
 unsigned need=all;
 int greedy=0;
 while(need){
  unsigned bm=0;int bg=0;
  for(auto &t:options){int g=__builtin_popcount(t.m&need);if(g>bg){bg=g;bm=t.m;}}
  need&=~bm;greedy++;
 }
 if(!gone && !bad && greedy<=nterms+2){
  vector<T> top, path;
  sort(options.begin(),options.end(),[](auto l,auto r){return __builtin_popcount(l.m)>__builtin_popcount(r.m);});
  for(auto t:options){bool seen=false;for(auto q:top)if((q.m&t.m)==t.m){seen=true;break;}if(!seen)top.push_back(t);}
  if(cover(top,unsigned(pos),nterms,path)){
   chosen=path;
   return 0;
  }
 }
 return 10*gone+10*bad+abs(greedy-nterms)+1;
}
int main(int argc,char**argv){
 nterms=atoi(argv[1]);k=22-2*nterms;rng.seed(atoi(argv[2]));
 int dur=atoi(argv[3]);ifstream f("oracle.txt");for(int j=0;j<11;j++)f>>z0[j];
 int pn,rows,ns;f>>pn>>rows>>ns;pos=(uint64_t(1)<<pn)-1;neg=((uint64_t(1)<<rows)-1)^pos;
 vector<vector<G>> maps;
 for(int s=0;s<ns;s++){
  vector<G> c; vector<int> originals(33,-1);
  for(int j=0;j<11;j++)originals[j]=j;
  for(int i=0;i<22;i++){
   G g;f>>g.a>>g.b>>g.o;
   if(g.o&&originals[g.a]>=0&&originals[g.b]>=0){
    originals[11+i]=11+c.size();c.push_back({originals[g.a],originals[g.b],1});
   }
  }
  maps.push_back(c);
 }
 const auto finish=chrono::steady_clock::now()+chrono::seconds(dur);
 uint64_t steps=0;
 while(chrono::steady_clock::now()<finish){
  vector<G> c=maps[rng()%maps.size()];c.resize(k);
  for(int i=0;i<k;i++)if(i>=k-2||c[i].a>=11+i||c[i].b>=11+i||(c[i].a==c[i].b))
   c[i]={int(rng()%(11+i)),int(rng()%(11+i)),int(i<k-2)};
  int sc=run(c);
  for(int t=0;t<8000;t++,steps++){
    int i=rng()%k,j=rng()%3, oldo=c[i].o; G old=c[i]; int i2=-1;
    if(j==0)c[i].a=rng()%(11+i);
    if(j==1)c[i].b=rng()%(11+i);
    if(j==2){
     int v=rng()%k;
     if(c[i].o==c[v].o)continue;
     i2=v; swap(c[i].o,c[v].o);
    }
    if(c[i].a==c[i].b){c[i]=old;if(i2>=0)c[i2].o=!oldo;continue;}
    int a=run(c);
    if(a<best){best=a;cout<<"best penalty "<<best<<" steps "<<steps<<endl;}
    if(a==0){
     for(auto g:c)cout<<g.a<<" "<<g.b<<" "<<g.o<<"\n";
     cout<<"terms\n";for(auto q:chosen)cout<<q.a<<" "<<q.b<<"\n";
     return 0;
    }
    if(a<=sc||(rng()%1000<unsigned((t%2000<500?110:40)/(max(1,a-sc)))))sc=a;
    else {c[i]=old;if(i2>=0)c[i2].o=!oldo;}
  }
 }
 cout<<"total steps "<<steps<<endl;
}
