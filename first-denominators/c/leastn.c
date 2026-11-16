// For primes p==1 mod 4 up to LIM: least n==3 mod 4 with r=n-(p mod n), 4r | n+1  (i.e. p = 4acd-a-c, n=4ad-1, r=a)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
int main(int argc,char**argv){
  uint64_t LIM=strtoull(argv[1],0,10); uint64_t NMAX=strtoull(argv[2],0,10);
  uint32_t sq=(uint32_t)sqrt((double)LIM)+2;
  char*small=calloc(sq+1,1); uint32_t*pr=malloc(sizeof(uint32_t)*(sq/2+10)); int np=0;
  for(uint32_t i=2;i<=sq;i++){ if(!small[i]){pr[np++]=i; for(uint64_t j=(uint64_t)i*i;j<=sq;j+=i) small[j]=1;}}
  const uint32_t SEG=1<<20; char*seg=malloc(SEG);
  uint64_t rec=0, cnt=0, fail=0; double sum=0; uint64_t hist[40]={0};
  for(uint64_t lo=2;lo<=LIM;lo+=SEG){
    uint64_t hi=lo+SEG-1; if(hi>LIM)hi=LIM; memset(seg,0,SEG);
    for(int i=0;i<np;i++){ uint64_t q=pr[i]; if(q*q>hi)break; uint64_t s=(lo+q-1)/q*q; if(s<q*q)s=q*q; for(uint64_t j=s;j<=hi;j+=q) seg[j-lo]=1; }
    for(uint64_t p=lo;p<=hi;p++){ if(seg[p-lo]||(p&3)!=1) continue; cnt++;
      uint64_t n; int ok=0;
      for(n=3;n<=NMAX;n+=4){ uint64_t r=n-p%n; if(((n+1)>>2)%r==0){ok=1;break;} }
      if(!ok){fail++; printf("FAIL p=%llu\n",(unsigned long long)p); continue;}
      sum+=n; int b=0; uint64_t t=n; while(t>1){t>>=1;b++;} hist[b]++;
      if(n>rec){rec=n; printf("record p=%llu n=%llu a=%llu  log2p^2=%.1f\n",(unsigned long long)p,(unsigned long long)n,(unsigned long long)(n-p%n),pow(log((double)p),2));}
    }
  }
  printf("primes %llu fail %llu mean n %.2f\n",(unsigned long long)cnt,(unsigned long long)fail,sum/cnt);
  for(int b=0;b<40;b++) if(hist[b]) printf("n in [2^%d,2^%d): %llu\n",b,b+1,(unsigned long long)hist[b]);
}
