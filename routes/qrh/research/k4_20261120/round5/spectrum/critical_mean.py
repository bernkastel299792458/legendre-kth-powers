"""Localized critical-line mean square with nested residue-class folds."""
from math import gcd, prod
from flint import arb


def critical_mean(U, W, logh, pieces=64, q=210, mix=None, *, base=6, fold=None):
    """Uniform multiplier for T log T in the weighted polynomial mean square."""
    T0 = U.exp()
    v, tau = arb(101)/100, arb(103)/100
    order = 2048
    ybar = v*order/(order-1)
    eps = (v*T0)**(-arb(1)/5)
    width = eps**3
    mass = 1-4*eps/arb.pi()
    corr = ((1+eps)*eps*(2*width).exp()).exp()/mass
    if not (mass>0 and U>20 and W>0 and 0<pieces):
        raise ValueError("unsupported critical mean parameters")
    h = logh.exp()
    sections = [(arb(0),W,arb(1),1/W)]
    last_width = W
    if mix is not None:
        last_width,theta = mix
        if not (last_width>W and 0<theta and theta<1):
            raise ValueError("mixed taper widths and weight")
        sections = [(arb(0),W,arb(1),(1-theta)/W+theta/last_width),
                    (W,last_width,theta*(1-W/last_width),theta/last_width)]
    X = (last_width+logh).exp()  # Physical endpoint divided by T
    primes = [p for p in (2,3,5,7,11) if q%p==0]
    if q%6 or prod(primes)!=q:
        raise ValueError("unsupported sieve modulus")
    if base not in (6,30,210) or q%base or (base!=6 and fold is None):
        raise ValueError("unsupported critical-line factorization")
    B = q//base
    rs = [r for r in range(1,B+1) if B%r==0]
    classes = {}
    for a in rs:
        groups = set(gcd(a,r) for r in rs)
        classes[a] = {g:2*prod(p-1 for p in primes if (a//g)%p==0) for g in groups}
    rho = 1/arb(2).zeta()
    # Laurent constant of the squarefree, coprime Dirichlet series.
    from flint import arb_series
    zeta2 = arb_series([2,1],prec=2).zeta()
    offset = arb.const_euler()-2*zeta2[1]/zeta2[0]
    for p in primes:
        rho *= arb(p)/(p+1)
        offset += arb(p).log()/(p+1)
    offset *= rho
    count_error = arb(2**len(primes)+2)
    if not h*T0>1:
        raise ValueError("taper head below squarefree counting range")
    def log_tail(s):
        total=arb(0)
        for lo,hi,initial,slope in sections:
            start=s.max(lo).min(hi)
            va,vb=initial-slope*(start-lo),initial-slope*(hi-lo)
            total+=(hi-start)*(va*va+va*vb+vb*vb)/3
        return total

    harmonic_offset = rho*(logh+log_tail(arb(0)))+offset+3*count_error/(h*T0).sqrt()
    def harmonic(cut):
        total_offset = arb(0)
        for r in rs:
            z = cut/r
            if not z*T0>1:
                raise ValueError("harmonic cutoff below counting range")
            if z<=h:
                total_offset += (rho*z.log()+offset+3*count_error/(z*T0).sqrt())/r
                continue
            if not z>h:
                raise ArithmeticError("ambiguous harmonic breakpoint")
            remove = log_tail((z/h).log())
            # Partial summation of the squarefree-counting discrepancy.
            # For weight omega(t)^2/t on (zT,XT], cost <= 3C/sqrt(zT).
            total_offset += (harmonic_offset-rho*remove+
                             3*count_error/(z*T0).sqrt())/r
        return rho*sum(arb(1)/r for r in rs)+total_offset.max(arb(0))/U

    def primitive(z):
        """Integral of the squared taper on [0,z], in units of T."""
        z = z.min(X)
        if z<=h:
            return z
        if not z>h:
            raise ArithmeticError("ambiguous taper breakpoint")
        result=h
        for lo,hi,initial,slope in sections:
            start,stop=h*lo.exp(),h*hi.exp()
            end=z.max(start).min(stop)
            val=initial-slope*((end/h).log()-lo)
            result+=end*(val*val+2*slope*val+2*slope**2)
            result-=start*(initial*initial+2*slope*initial+2*slope**2)
        return result

    def energy(lo,hi,r):
        lo,hi = (lo/r).min(X), (hi/r).min(X)
        if lo>=hi:
            return arb(0)
        return ((primitive(hi)-primitive(lo))*rho+
                2*count_error*(hi/T0).sqrt()).max(arb(0))

    if fold is not None:
        return fold(base, B, rs, v, tau, order, ybar, eps, width, corr, U, X, pieces,
                    harmonic, energy, rho, harmonic_offset)
    small = 6*v*tau*(1+eps)/arb.pi()
    end = B*X
    if not end>small:
        raise ValueError("frequency cells do not intersect support")
    overlap = width.exp()
    # Below small*T use the affine modulus-6 mean. On the middle band
    # the folded interval has at most one row at almost every phase.
    hs = harmonic(small*overlap)
    unweighted = arb.pi()/3*sum(energy(arb(0),small*overlap,r) for r in rs)
    # Subdivide at every new single-row threshold. Above it, any previously
    # available modulus may still give the smaller norm for this band.
    allowed = [a for a in rs if small*a<end]
    for i,a in enumerate(allowed):
        start = small*a
        stop = small*allowed[i+1] if i+1<len(allowed) else end
        count = max(1,int(float(pieces*(stop/start).log()/(end/small).log()))+1)
        ratio = (stop/start)**(arb(1)/count)
        for j in range(count):
            lo = start*ratio**j
            hi = stop if j+1==count else start*ratio**(j+1)
            energies = {r:energy(lo,hi*overlap,r) for r in rs}
            best = arb.pi()/3*sum(energies.values())
            for b in allowed[1:i+1]:
                weights = classes[b]
                group_cost = sum((size*sum(e for r,e in energies.items() if gcd(b,r)==g)).sqrt()
                                 for g,size in weights.items())
                best = best.min(arb.pi()/(6*b)*group_cost**2)
            unweighted += best
    # The remote time tail retains the full old modulus-6 inequality.
    # Its diagonal may use the full harmonic norm instead of subtracting hs.
    remote_prob = tau**(-order)
    remote_mean = ybar*tau**(1-order)
    harmonic_all = sum(arb(1)/r for r in rs)*(rho+harmonic_offset.max(arb(0))/U)
    ordinary_energy = arb.pi()/3*sum(energy(arb(0),end,r) for r in rs)
    return corr*((1+eps)*(ybar*hs+remote_mean*harmonic_all)
                 +(unweighted+remote_prob*ordinary_energy)/U)
