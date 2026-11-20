# A Gaussian zero detector in the finite box

Claude and Codex research workspace. Codex derived this reduction and its finite arithmetic. Assume \(\Re\rho\le\Theta=7/8\), and the published height of verified RH, \(H=3000175332800\). For \(H\le T\le e^{45}\), write \(u=\log T\) and \(R_s=7uT^{p_s}\), where \(p_s=3(1-s)/(3s-1)\) and \(s=.800,.801,\ldots,.874\). All counts below include multiplicities. This note leaves open a signed large-value estimate. The \(\rho\)'s counted have \(H<\gamma\le T,\ \beta>s\). [Finite-height RH](https://arxiv.org/abs/2004.09765) · [Sufficiency of this zero count for the fourth-power problem](../../spectrum/DENSITY_TARGET.md)

## A single signed tail

Use the short polynomial \(P\) of [SHORT.md](../SHORT.md) with \(Q=210,\ N=32768\) and the sharp cutoff. Its coefficient at each \(d\le N\) is \(\mu(d)\). Thus the coefficients \(a(n)\) of \(\zeta P\) have \(a(1)=1,\ a(n)=0\) for \(1<n\le N\). At every prime \(p>N\), \(a(p)=1\). Set \(D=3/8,\ b=\sqrt{2}D,\ Y=c_Y T\), and let \(\Phi\) be the standard Gaussian distribution function. Put
\[
 D_Y(z)=\sum_{n>N}a(n)n^{-z}\Phi(b\log(Y/n)).
\]
Absolute convergence at every \(z\) follows from the Gaussian tail. For \(d_\rho=\beta-1/2\), Mellin inversion and shifting to the critical line give
\[
 \Phi(b\log Y)+D_Y(\rho)=
 P(1)\,Y^{1-\rho}\frac{\exp((1-\rho)^2/(2b^2))}{1-\rho}+I_\rho ,
\quad
 I_\rho=\frac{Y^{-d_\rho}}{2\pi}\int_{\mathbb R}
 (\zeta P)(1/2+i(\gamma+v))Y^{iv}
 \frac{\exp((-d_\rho+iv)^2/(2b^2))}{-d_\rho+iv}\,dv .
\]
The Mellin kernel is \(\exp(w^2/(2b^2))/w\). Its pole at \(w=0\) has residue zero when multiplied by \((\zeta P)(\rho+w)\). Gaussian decay justifies the horizontal contour limits using Euler summation in the bounded vertical strip (which supplies polynomial growth). For \(c_Y=128,512\), the pole contribution has modulus less than \(10^{-40}\), as \(|P(1)|\le210N\), \(\gamma>H\) and \(\log Y<52\). Also \(\Phi(b\log Y)>1-10^{-30}\). Every zero with \(|I_\rho|<1/2\) therefore satisfies the **signed** inequality \(\Re D_Y(\rho)<-.4999\).

## A direct count for the critical integral

Write \(c=2s-1/2>1,\ a_\rho=c-\beta>0\). Then \(a_\rho\le d_\rho\) for every zero in the set. For \(P_a(v)=a/(a^2+v^2)\), Cauchy–Schwarz on \(|v|\le40\) gives
\[
 |I_{\rho,\mathrm{near}}|^2
 \le Y^{1-2s}J_s\int_{-40}^{40}
 |(\zeta P)(1/2+i(\gamma+v))|^2 P_{a_\rho}(v)\,dv,\qquad
 J_s=\frac{e^{D^2/b^2}\sqrt{\pi}b}{4\pi^2(c-\Theta)}.
\]
Indeed, after division by \(P_{a_\rho}\) the squared absolute analytic kernel is bounded by
\(e^{D^2/b^2}e^{-v^2/b^2}/(4\pi^2(c-\Theta))\), using
\((a_\rho^2+v^2)/(d_\rho^2+v^2)\le1\). On \(|v|\ge40\) the omitted integral has modulus below \(10^{-40}\): use \(|\zeta(1/2+it)|\le6\sqrt{|t|+1}\) from [FAST_SHORT.md](../FAST_SHORT.md), \(|P|\le210N\), \(|-d_\rho+iv|\ge.3\), and \(e^{-v^2/(2b^2)}\le e^{-40|v|}\). The factor \(\sqrt{|\gamma+v|+1}\le\sqrt{T+1}(1+|v|)\) leaves an elementary exponential tail.

For \(H-40\le t\le T+40\), the positive Poisson kernels summed over the selected zeros are bounded by the sum over all nontrivial zeros. The real part of the Hadamard product for \(\xi\) gives
\[
 \sum_{\rho\ {\rm all}}P_{c-\beta}(t-\gamma)
 =\Re\left[\frac1z+\frac1{z-1}-\frac12\log\pi
      +\frac12\psi(z/2)+\frac{\zeta'}{\zeta}(z)\right],\qquad z=c+it.
\]
The constant in the product cancels on taking real parts by symmetry \(\xi(z)=\xi(1-z)\). The right side is at most
\(F_s(u)=\tfrac12(u-\log(2\pi))-\zeta'(c)/\zeta(c)+.001\).
For the last Dirichlet series use absolute convergence. The digamma bound follows by Euler summation, since
\(\left|\psi(z/2)-\log(z/2)\right|\le 1/|z|+\pi/(2|t|)\). Indeed the Euler remainder is bounded by
\(\frac12\int_0^\infty |z/2+x|^{-2}dx\le\pi/(2|t|)\). The displayed slack also absorbs the two rational terms and \(\log(|z|/T)/2\).

Let \(S(U)\) denote the certified coefficient of \(Z\log Z\) in the short joint second moment of \(\zeta P\) for \(Z\ge e^U\). Then, for \(u\in[U,V]\), the number \(B_s(T)\) of zeros with \(|I_\rho|\ge1/2\) satisfies
\[
 \frac{B_s(T)}{R_s}
 \le \frac{1.00000001 J_s F_s(V) S(U)}{7(1/2-10^{-40})^2}
  \ c_Y^{1-2s}
  \max_{w\in\{U,V\}} e^{(2-2s-p_s)w}.
\]
Only positive heights up to \(T+40\) occur in the truncated integral. The leading slack bounds \((T+40)\log(T+40)/(T\log T)\). The script evaluates all 75 nodes and all closed height cells of width \(1/8\) intersecting \([\log H,45]\). The largest certified ratio is below **0.099760** for \(c_Y=128\) and **0.041427** for \(c_Y=512\). At \(T=e^{35},s=.85\) these estimates give at most **418282** and **158499** zeros, respectively, against the total target \(6341009.45091\). These bounds use the floor of the rigorous real upper bound. Rerunning with \(\theta\) for the Type II threshold replaces \(1/2-10^{-40}\) by \(\theta-10^{-40}\).

In particular one remaining sufficient lemma on the full target box would be
\[
 \#\{\rho:\beta>s,\ H<\gamma\le T,\ \Re D_{512T}(\rho)<-.4999\}
 \ \le\ 6.70(\log T)T^{p_s}.
\]
Adding the certified critical-integral part proves the required \(7(\log T)T^{p_s}\). This is a single smoothed signed Dirichlet tail. The following calculation explains why treating its individual dyadic large values independently is problematic.

## A lower bound on the cost of the usual block argument

Fix \(T=e^{35},s=.85\). Write \(R=R_s\), and let \(m=2^j\) with \(15\le j\le48\). For a sharp block \(m<n\le2m\), grant an optimistic counting model using any integer power \(k\ge1\). Let \(G_k\) be the squared coefficient norm of the \(k\)-th power, including \(n^{-\beta}\) and the Gaussian weight. If \(\lambda\) is the block threshold, consider these two relaxed costs:
\[
 \max(T,m^k)G_k\lambda^{-2k},\qquad
 \max(m^kG_k\lambda^{-2k},T m^k G_k^3\lambda^{-6k}) .
\]
These are the classical mean-square and Halász–Huxley shapes with all leading constants and logarithmic and spacing losses removed, \(m^k\) used as length, and a maximum replacing an addition. The calculation concerns proofs using these specific expressions and additive allocation of block thresholds. It does not lower-bound true counts, improved large-value techniques, or bounds keeping correlations between blocks. [Huxley, large values, §2](https://matwbn.icm.edu.pl/ksiazki/aa/aa26/aa2648.pdf) · [Guth–Maynard's discussion of the classical estimates](https://ora.ox.ac.uk/objects/uuid%3Aad11b8bf-ad2b-4ebf-a627-647f023c378f/files/s73666708v)

Take \(v_p=\Phi(b\log(Y/p))p^{-\beta}\). A product of exactly \(k\) primes from the block admits only prime factors in each of the \(k\) multiplicands of its Dirichlet coefficient, since each multiplicand exceeds one. Thus its coefficient is a positive multinomial multiple of \(\prod v_p\), independently of the signs of the other coefficients. If \(g\) is any lower bound on \(\sum_{m<p\le2m}v_p^2\), then
\[
 G_k\ge g^k\max\left(1,k!\left[1-\binom{k}{2}m^{-2s}/g\right]_+\right)=g^k b_k .
\]
The baseline counts ordered tuples. For the factorial improvement take distinct-prime tuples and apply the union bound for a collision under the probability law proportional to \(v_p^2\). Each collision probability is at most \(m^{-2s}/g\).

For the first eleven blocks a sieve of Eratosthenes counts primes exactly in 16 subintervals per block. On each subinterval of upper endpoint \(r\), use \(v_p^2\ge .999^2 r^{-2\Theta}\), as \(r\le2^{26}\). On the other 23 blocks use \(v_p^2\ge .99^2(2m)^{-2\Theta}\). The two Gaussian lower bounds hold already for \(Y=128T\), and increase with \(Y\). Rosser–Schoenfeld gives the prime-count lower bound \(2m/\log(2m)-1.25506m/\log m\) here. [Rosser–Schoenfeld, Corollary 1, equations (3.5)–(3.6)](https://doi.org/10.1215/ijm/1255631807)

Even to make one of the two cost formulas at most the entire budget \(R\), one needs
\[
 \lambda\ge\sqrt{g}\ b_k^{1/(2k)}
 \min\left\{\left(\frac{\max(T,m^k)}R\right)^{1/(2k)},\
 \max\left(\sqrt m\,R^{-1/(2k)},\
   m^{1/6}(T/R)^{1/(6k)}\right)\right\}.
\]
Enumerate \(1\le k\le7\); for \(k\ge8\) both bounds imply \(\lambda\ge\sqrt{gm}\,R^{-1/16}\). Summing the per-block minima yields more than **0.7065884** on the first eleven blocks and **1.0197871** on all 34. Thus allocating the full unit of detection amplitude cannot suffice within this independent-block model, even when every block is granted the full count budget.

The stronger test allocates fractions \(f_j>0\) with \(\sum_j f_j\le1\) and substitutes \(R f_j\) for \(R\). If \(q_j(f)\) is the resulting per-block threshold lower bound, then, for every fixed \(\mu\ge0\),
\[
 \sum_j\lambda_j\ge\sum_j\inf_{0<f\le1}(q_j(f)+\mu f)-\mu .
\]
For \(A f^{-h}+\mu f\) the optimizing \(f\) is \(\min(1,(hA/\mu)^{1/(1+h)})\). A minimum over finitely many choices of \(k\) commutes with taking the infimum; for a maximum of two terms use the maximum of their infima as a lower bound. When \(k\ge8\), the valid common pointwise lower bound is \(\sqrt{gm}\min(1,(Rf)^{-1/16})\), including \(Rf<1\). The script tests sixteen fixed dual multipliers. The same prime coefficients work for the larger sharp mollifiers once the first block starts at that new \(N\).

| \(N\) | Necessary total threshold with the whole count budget available to Type I |
|---:|---:|
| \(2^{15}\) | \(>1.71658\) |
| \(2^{19}\) | \(>1.14660\) |
| \(2^{20}\) | \(>1.03941\) |
| \(2^{21}\) | \(>.94790\) |
| \(2^{22}\) | \(>.86981\) |

For example at \(N=2^{21}\), \(s=.85,\ T=e^{35},\ Y=512T\), the same mixed second moment gives \(S(35)<3.17222\). Type II with threshold \(0.25\) then costs under \(0.329R\), or under \(0.168R\) with threshold \(0.35\). Type I can use a detection amplitude slightly below \(0.75\) or \(0.65\), respectively. The optimistic lower bound \(0.94790\) exceeds both possibilities even on allocating the *entire* \(R\) to Type I. The required finite bound for the unsplit signed tail is still open.

Run **python -B gaussian_detector.py** to reproduce the Gaussian and block certificates. The analytic inputs and arithmetic are documented in this note and [FAST_SHORT.md](../FAST_SHORT.md). This work does not provide an end-to-end formal verification.
