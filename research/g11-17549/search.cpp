#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
struct G{int a,b,o;};
using C=array<G,21>;
uint64_t raw[11], pos, neg;
void eval(const C& c,int &p,int &n,int &u){
 uint64_t z[32];for(int i=0;i<11;i++)z[i]=raw[i];
 for(int i=0;i<21;i++)z[11+i]=c[i].o?(z[c[i].a]|z[c[i].b]):(z[c[i].a]&z[c[i].b]);
 p=__builtin_popcountll(pos&~z[31]);n=__builtin_popcountll(neg&z[31]);u=0;
 // Evaluating dead gates is cheap; prefer using all topology once close.
 if(p+n<=3){
   unsigned need=1U<<31;for(int i=20;i>=0;i--)if(need&(1U<<(11+i)))need|=(1U<<c[i].a)|(1U<<c[i].b);
   u=21-__builtin_popcount(need>>11);
 }
}
int main(int argc,char**argv){
 mt19937 rng(argc>1?strtoul(argv[1],nullptr,10):1);
 int seconds=argc>2?atoi(argv[2]):60;
 ifstream f("oracle.txt");for(auto &v:raw) f>>v;
 int pnum,N,ns;f>>pnum>>N>>ns;
 pos=(1ULL<<pnum)-1;neg=(N==64?~0ULL:((1ULL<<N)-1))^pos;
 vector<array<G,22>> seeds(ns);for(auto &s:seeds)for(auto &g:s)f>>g.a>>g.b>>g.o;
 const auto end=chrono::steady_clock::now()+chrono::seconds(seconds);
 uint64_t steps=0; int best=100;
 for(int attempt=0;chrono::steady_clock::now()<end;attempt++){
  C c;
  auto &s=seeds[rng()%ns];int k=rng()%21, side=rng()%2;
  auto a=[&](int x){if(x==11+k)x=side?s[k].b:s[k].a;return x-(x>11+k);};
  for(int i=0,j=0;i<22;i++){if(i!=k){c[j++]={a(s[i].a),a(s[i].b),s[i].o};}}
  int P,N,U;eval(c,P,N,U);
  const int negw=2+rng()%5,posw=2+rng()%5;
  int sc=P*posw+N*negw+U;
  for(int t=0;t<20000;t++,steps++){
   int i=rng()%21,how=rng()%7;G old=c[i];int bound=11+i;
   if(how<=1)c[i].a=rng()%bound;
   else if(how<=3)c[i].b=rng()%bound;
   else if(how==4)c[i].o^=1;
   else if(how==5)c[i]={int(rng()%bound),int(rng()%bound),int(rng()%2)};
   else { if((rng()&1)&&i>0)c[i].a=bound-1;else c[i].b=rng()%11;}
   int P2,N2,U2;eval(c,P2,N2,U2);
   if(P2+N2<best){best=P2+N2;cout<<"best "<<best<<" p "<<P2<<" n "<<N2<<" attempt "<<attempt<<" steps "<<steps<<endl;}
   if(P2+N2==0){for(auto g:c)cout<<g.a<<" "<<g.b<<" "<<g.o<<"\n";return 0;}
   int score=P2*posw+N2*negw+U2;
   int jitter=(t%3000<600)?11:6;
   if(score<=sc || ((rng()%1024)<unsigned(1U<<max(0,jitter-(score-sc)*2)) ))sc=score;
   else c[i]=old;
  }
 }
 cout<<"steps "<<steps<<" best "<<best<<endl;
}
