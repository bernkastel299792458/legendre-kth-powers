# All large moduli in a presieved physical interval

At \(L=116,\ K=H,\ z=1732099\sqrt{e^{116}/H}\), one has \(z^2<e^{c-r}\), where \(c=L+\frac12\log(1+4e^{-L/4})\) and \(r=10^{-6}\). Fix a squarefree \(Q\), restrict integers and sieve divisors to be relatively prime to \(Q\), and write \(\eta=\varphi(Q)/Q\). If \(p\) is the smallest integer greater than one coprime to \(Q\), the entire region \(q=[d,e]>e^{c+r}/p\) has no actual admissible multiple. The integer multiplier 1 puts the location below \(e^{c-r}\). Every other admissible multiplier is at least \(p\), putting the location above \(e^{c+r}\). This treats all near positive lobes and all Fourier frequencies simultaneously.

The following are additive upper bounds on the resulting normalized signed remainder, obtained by subtracting the actual presieved main term. They cover exactly the indicated large-modulus part. Smaller moduli and the other terms in the fourth-power inequality require separate estimates.

| \(Q\) | First admissible integer \(p>1\) | Ordered gcd/dyadic cells | With the finite mean Mertens table | With published Mertens inputs only |
|---:|---:|---:|---:|---:|
| 2 | 3 | 3 | .000007053 | .00083198 |
| 6 | 5 | 6 | .000021593 | .00220111 |
| 30 | 7 | 6 | .000034059 | .00298370 |
| 210 | 11 | 10 | .000077030 | .00551713 |

With \(G_v(y)=\sum_{n\le y,(n,v)=1}\mu^2(n)/\varphi(n)\), the presieved coefficients are \(\lambda_d=\mu(d)\rho(d)G_{Qd}(z/d)/G_Q(z)\), \((d,Q)=1\). The bulk main term per pair is \(\eta y/q\), by the exact density of available multiples. The lower bound \(G_Q(z)\ge\eta G_1(z)\) follows by partitioning the squarefree indices in \(G_1(z)\) according to their gcd with \(Q\) and enlarging each resulting positive sum to \(G_Q(z)\). The exact large-region remainder is therefore \(-\eta y\sum_{\rm large}\lambda_d\lambda_e/q\).

The proof of the full and cut rectangle estimates in [the original row calculation](EMPTY_LCM.md) now requires \((g,Q)=1\). In the one-variable convolution one adds \(Q\) to the conductor, making the local factor \(R_s(Qgbh)\); submultiplicativity permits \(R_s(Qgb)\,R_s(h)\) exactly as before. Both the absolute and signed \(b\)-sums are over \((b,gQ)=1\). The positive \(h\)-norm can still be enlarged to all \(h\). No other factor changes. The implementation uses the conservative \(\eta(\log z+1.331)\) below \(G_Q(z)\), and multiplies the inverse moment by \(\eta\). In particular its output does not require a more precise asymptotic for the presieved denominator.

~~~powershell
python -B round8/physical_low/presieved_empty.py --Q 2 --mean --upper .000007053
python -B round8/physical_low/presieved_empty.py --Q 2 --upper .00083198
python -B round8/physical_low/presieved_empty.py --Q 2 6 30 210 --mean
~~~

## First admissible multiple immediately below the empty slice

The empty range ends at \(q=e^{c+r}/p\). On the adjacent narrow physical strip \(n=pq\) with \(n\) lying in either first lobe, \(q>z^2/p\) since \(z^2<e^{c-r}\). As \((d,e)\) is coprime to \(Q\), it is either 1 or at least \(p\). The latter implies \(de\ge pq>z^2\), which is impossible. Thus every admissible pair at the first true multiplier has gcd 1, and every pair at the same squarefree \(q\) has the same sign \(\mu(q)\).

The actual normalized mass with absolute values after aggregating the coefficient of each \(q\) has the following lower bounds on the union of the two first lobes.

| \(Q\) | First physical multiplier | Charge exceeds |
|---:|---:|---:|
|2|3|.0040841|
|6|5|.0037544|
|30|7|.0031220|
|210|11|.0023032|

Use the [short squarefree-row lower bound](SPIKE_FLOOR.md) on \((m/k,(m+y)/k]\), with \(k=p\). Let \(P=23\) (at least every prime of the four \(Q\)), \(x_h=e^{c+b/K}\), \(x_l=e^{c-b/K}\), \(A=x_h/(kz), M=x_l/(kz),\ell=\log(z/A)\). Require both indices individually coprime to \(Q\), in addition to joint coprimality and squarefreeness. Define
\[
 U=\prod_{\substack{p'\le P\\p'\nmid Q}}\rho(p'),\quad D=2^{\pi(P)}U,\quad
 p_0=\eta^2\prod_{\substack{p'\le P\\p'\nmid Q}}(1-(p')^{-2}).
\]
The conditional inner mean now has a factor \(\eta\). After multiplication by the outer small-prime weight one gets \(\eta\) times the indicator of being coprime to \(Q\) and squarefree at the other primes up to \(P\). The mean of this weighted outer indicator is \(p_0\); its interval discrepancy is at most \(\eta 2^{\pi(P)}\) by divisibility expansion. Thus the previous formula for \(S_0\) has \(p_0-3\eta S\) in its first term and an additional factor of \(\eta\) multiplying its second term. Its final tail term and \(E\) use the stated updated \(U,D\).

In the normalization, use the same one-lobe area and sum the two identical lower bounds; the position derivative is now bounded below by \(x_l/K\). The \(y\)-slope gains \(1/k\), while the additive discrepancy does not. For an upper bound on the denominator, the positive gcd splitting yields
\[
 G_Q(z)\le G_1(z)-\eta\sum_{d\mid Q,d>1}G_1(z/d)/\varphi(d)
 \le\eta(\log z+1.34)+\sum_{p'\mid Q}\frac{\log p'}{p'}
             +2.44(1+\sqrt Q)/\sqrt z .
\]
Here \(z>Q\) in all applications. This proves the table via the elementary integer count alone. To compare with the previous empty-slice table, these are lower bounds on positive unsigned charges, not signed estimates.

~~~powershell
python -B round8/physical_low/presieved_spike.py --Q 2 --k 3 --lower .0040841
python -B round8/physical_low/presieved_spike.py --Q 6 --k 5 --lower .0037544
python -B round8/physical_low/presieved_spike.py --Q 30 --k 7 --lower .0031220
python -B round8/physical_low/presieved_spike.py --Q 210 --k 11 --lower .0023032
~~~

The adjacent *second* admissible multiplier also gives a lower bound after exact same-modulus aggregation for each of these four primorials. Let \(p,p'\) be the first two integers \(>1\) coprime to \(Q\), both prime in the cases at hand. If \(q>z^2/p'\), its gcds can only be 1 or \(p\). Moduli not divisible by \(p\) have gcd 1. For \(q=pr_0\), expand over ordered \(uv=r_0\) with \((u,vpQ)=(v,pQ)=1\) using the three placements of \(p\), just as in [the same-modulus identity](SIGNED_MODULUS.md). For \((u,pQ)=1\),
\[
 \lambda_u+\lambda_{pu}=\frac{\mu(u)\rho(u)}{G_Q(z)}
 \big[G_{Qpu}(z/u)-G_{Qpu}(z/(pu))\big].
\]
In particular \(|\lambda_{pu}|\le|\lambda_u|\). If both \(pu,pv\) are admissible, the absolute modulus coefficient for this ordered pair of odd-part analogues is at least \(|\lambda_{pu}\lambda_{pv}|\), which pays \(\rho(p)/2\) times the two baseline coprime placements \(\rho(pu)\rho(v)+\rho(u)\rho(pv)\), after the common denominator is included. If only one placement is possible there is no cancellation. Each resulting contribution has sign \(\mu(q)\). At the actual second multiplier one has \(q=n/p'>z^2/p'\) on both lobes. The \(q\)-bands for the two multipliers are disjoint. Consequently the sum of the *true* absolute coefficients over both sets of moduli has normalized physical mass exceeding .0067697 for \(Q=2\) and .0057748 for \(Q=6\), from the first table and the additional charges \( \tfrac34 (.00358083)\) and \( \tfrac58 (.00323265)\), respectively.

~~~powershell
python -B round8/physical_low/presieved_spike.py --Q 2 --k 5 --lower .00358083
python -B round8/physical_low/presieved_spike.py --Q 6 --k 7 --lower .00323265
~~~

In these two commands the program's boolean only tests whether all gcds are forced to 1. The displayed unaggregated lower bounds require the factors just proved when both possible gcds occur.
