"""Integer-only segment certificate for reciprocal Mobius on the 2310 units."""
import argparse
from math import isqrt
import numpy as np
from numba import njit,prange,set_num_threads,config


@njit(parallel=True,cache=False)
def segments(stop,step,ps):
    count=(stop+step-1)//step
    out=np.zeros((count,3),dtype=np.int64)
    for j in prange(count):
        start=j*step+1
        last=min(stop,(j+1)*step);length=last-start+1
        mu=np.ones(length,dtype=np.int8)
        rest=np.arange(start,last+1,dtype=np.int32)
        for h in range(len(ps)):
            p=int(ps[h])
            if p*p>last:break
            i=(-start)%p
            if 2310%p==0:
                for k in range(i,length,p):mu[k]=0
            else:
                for k in range(i,length,p):
                    mu[k]=-mu[k]
                    rest[k]//=p
                for k in range((-start)%(p*p),length,p*p):mu[k]=0
        acc=lo=hi=np.int64(0)
        for k in range(length):
            n=start+k
            if mu[k]==0:continue
            sign=mu[k]
            if rest[k]>1:
                if 2310%rest[k]==0:continue
                sign=-sign
            base=(np.int64(1)<<52)//n
            acc+=sign*base
            lo=min(lo,acc);hi=max(hi,acc)
        out[j,0]=acc;out[j,1]=lo;out[j,2]=hi
    return out


def run(power=30,block=18,workers=3):
    assert 20<=power<=30 and 12<=block<=19
    set_num_threads(min(workers,config.NUMBA_NUM_THREADS))
    top=2**power;step=2**block;L=isqrt(top)
    prime=np.ones(L+1,dtype=bool);prime[:2]=False
    for p in range(2,isqrt(L)+1):
        if prime[p]:prime[p*p::p]=False
    blocks=segments(top,step,np.asarray(np.flatnonzero(prime),dtype=np.int64))
    cur=0;out=[]
    for i in range(power):
        if 2**i<step:continue
        l=(2**i)//step;r=(2**(i+1))//step
        if not out:cur=int(sum(int(x[0]) for x in blocks[:l]))
        lo=hi=cur
        for total,minus,plus in blocks[l:r]:
            lo=min(lo,cur+int(minus));hi=max(hi,cur+int(plus))
            cur+=int(total)
        # Rounding towards zero introduces at most one lattice unit per n.
        m=max(-lo,hi)+2**(i+1)
        value=(m*10**9+2**52-1)//2**52
        out.append((i,value))
        print(i,value,flush=True)
    return out


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--power',type=int,default=30);ap.add_argument('--threads',type=int,default=3)
    a=ap.parse_args();run(a.power,workers=a.threads)
