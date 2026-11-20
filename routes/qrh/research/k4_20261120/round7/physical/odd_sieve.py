"""Selberg weights on the odd integers and their reciprocal bilinear rows."""
from functools import lru_cache,partial
from fractions import Fraction
from itertools import combinations
from math import gcd,lcm,prod
from types import FunctionType
from flint import arb, ctx, fmpz
from extras import weight_energy as energy
from bilinear import rational,upper


@lru_cache(None)
def convolution_norm(modulus,precision):
    assert precision == ctx.prec
    s=arb(3)/4
    norm=arb(1)
    for p in range(2,1001):
        if fmpz(p).is_prime():
            norm*=1+arb(p)**(-s) if modulus%p==0 else 1+(arb(p)**(-s)+p*arb(p)**(-2*s))/(p-1)
    m=arb(1000)
    tail=(m**(-s)/s+m**(1-2*s)/(2*s-1))*(1+1/m)
    return norm*tail.exp()


@lru_cache(None)
def parameters(modulus,precision):
    s=arb(3)/4
    primes=[int(p) for p,a in fmpz(modulus).factor() if a==1]
    assert precision==ctx.prec and prod(primes)==modulus and all(p<=1000 for p in primes)
    eta=arb(int(fmpz(modulus).euler_phi()))/modulus
    shift=sum(arb(p).log()/p for p in primes)
    error=(2+arb.const_euler()+1/(arb(1).exp()*(1-s)))*convolution_norm(modulus,ctx.prec)
    return eta,shift,error


def denominator(z,modulus=2):
    eta,shift,error=parameters(modulus,ctx.prec)
    return eta*(z.log()+arb("1.33258")+shift)-error/z.sqrt().sqrt()


@lru_cache(None)
def upper_harmonic(v,modulus,precision):
    eta,shift,error=parameters(modulus,precision)
    z=arb(v)
    return eta*(z.log()+arb("1.332583")+shift)+error/z.sqrt().sqrt()


@lru_cache(None)
def ratio(limit,modulus):
    size=1
    bound=Fraction(1)
    for p in range(2,401):
        if modulus%p==0 or not fmpz(p).is_prime():continue
        size*=p
        if size>limit:return bound
        bound*=Fraction(p,p-1)
    raise ValueError("insufficient primes")


def suprema(G,z,blocks,modulus):
    bound=rational(ratio(int(z.upper().ceil().unique_fmpz()),modulus))
    out=[]
    for i in range(blocks):
        v=2**(i+1)
        if v<=energy.N:
            mass=arb(int(energy.coprime_prefix(modulus)[v]))/energy.QUANT
        else:
            mass=upper_harmonic(v,modulus,ctx.prec).min(arb(v).log()+2+arb("2.44")/arb(v).sqrt())
        out.append(upper((bound*mass/G).min(arb(1))))
    return energy.np.array(out)


def unit_rows(known,blocks,precision,modulus):
    return energy.fixed_rows(modulus*known,blocks,precision,modulus)


def unit_factors(groups,blocks,G,z,modulus):
    rows=partial(unit_rows,modulus=modulus)
    func=FunctionType(energy.factors.__code__,dict(vars(energy),fixed_rows=rows,
                      max_ratio=partial(ratio,modulus=modulus),lambdas=partial(suprema,modulus=modulus)),
                      "unit_factors",energy.factors.__defaults__)
    return func(groups,blocks,G,z,z)


def harmonics(modulus):
    primes=[int(p) for p,a in fmpz(modulus).factor() if p!=2 and a==1]
    for k in range(len(primes)+1):
        for block in combinations(primes,k):
            m=prod(block)
            yield modulus//m,arb(prod(p-2 for p in block))/m


def unit_groups(groups,modulus):
    out=groups[[a!=b or gcd(int(a),modulus)==1 for a,b,_ in groups]].copy()
    period=lcm(energy.P**2,modulus)
    unit=energy.np.ones(period+1,dtype=energy.np.int64)
    for p in energy.SMALL:
        unit[::p if modulus%p==0 else p*p]=0
    for p,_ in fmpz(modulus).factor():
        unit[::int(p)]=0
    unit[0]=0
    count=energy.np.cumsum(unit)
    mean=Fraction(int(count[-1]),period)
    err=period*count-energy.np.arange(period+1,dtype=energy.np.int64)*int(count[-1])
    discrepancy=Fraction(int(max(err)-min(err)),period)
    for k,(a0,b0,old) in enumerate(out):
        a,b=int(a0),int(b0)
        if a==b:continue
        if b<8192:
            mass=sum((arb(1)/(n*n) for n in range(a,b+1)
                      if gcd(n,modulus)==1 and fmpz(n).moebius_mu()),arb(0))
        else:
            unrestricted=Fraction(1,a*a)+Fraction(1,a)-Fraction(1,b)
            mass=rational(mean*unrestricted+discrepancy/Fraction(a*a))
        out[k,2]=min(old,upper(mass))
    return out
