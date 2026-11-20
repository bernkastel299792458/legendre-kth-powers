# The absolute charge of a single genuine multiple

At \(x=e^{116},\ z=3000000\sqrt{x/H}\), an unconditional lower bound for one part of the physical Selberg remainder before cancellation is **.0047443**. This is the contribution of the actual absolute coefficients \(|\lambda_d\lambda_e|\), with \((d,e)=1\), the single multiple \(de\), and the first positive lobe to the right of the prime-free interval. Every such modulus satisfies \(q=de>x\). The existing normalized remainder allowance is **.003951058**. Even replacing the ordinary near-region Selberg main term by its true integral leaves less than **.004207**. Thus the approach that adds separate absolute multiple charges to that main term fails at this point. A signed sum can still be smaller.

Use \(K=H=3000175332800,\ L=116,\ c=L+\tfrac12\log(1+4e^{-L/4}),\ a=(1-10^{-12})K(c-L),\ b=2\pi-a,\ I=\pi\sin(a)/a\). Let \(x_h=\exp(c+b/K),\ A=x_h/z,\ M=x/z,\ \ell=\log(z/A)\). In any interval \((m,m+y]\) contained in the forward first lobe, retain \(A<d\le z,\ m/d<e\le(m+y)/d\). These inequalities imply \(0<e\le z\) and \(m/d\ge M\). For squarefree \(d,e\) one has \(G^2|\lambda_d\lambda_e|\ge\rho(d)\rho(e)\), with \(G=\sum_{n\le z}\mu^2(n)/\varphi(n)\) and \(\rho(n)=n/\varphi(n)\). Ordered pairs are the terms appearing in the actual square.

## A uniform lower bound for the interval

Take \(P=23,\ B_0=10^6,\ B=z^{1/3}\). Write \(w_P(n)\) for the product of the local squarefree weights at the primes \(p\le P\): it is zero at a multiple of \(p^2\), equal to \(\rho(p)\) at valuation one and otherwise one. Define
\[
 U=\prod_{p\le P}\rho(p),\quad D=\prod_{p\le P}2\rho(p),\quad
 p_0=\prod_{p\le P}(1-p^{-2}),\quad
 S=\sum_{P<p\le1000}p^{-2}+10^{-3}.
\]
The last expression bounds \(\sum_{p>P}p^{-2}\) by the integral test.

Fix \(d\). In the inner \(e\)-row impose \((d,e,\prod_{p\le P}p)=1\) in the sense that no prime \(p\le P\) divides both \(d\) and \(e\). Its frequency with weight \(w_P(e)\) is \(C_d=\prod_{p\mid d,\ p\le P}(1-1/p)\). For each \(p\le P\) not dividing \(d\), the divisibility expansion has coefficients \(1,\rho(p)-1,-\rho(p)\) at \(1,p,p^2\), with mean one and coefficient norm \(2\rho(p)\). For \(p\mid d\) use \(1-{\bf1}_{p\mid e}\). It follows that the discrepancy on any half-open interval has absolute value at most \(D\), including when an independent divisibility by \(h\), \((h,\prod_{p\le P}p)=1\), is imposed and the main term is divided by \(h\). In particular \(w_P(d) C_d\) equals the indicator that no \(p^2\), \(p\le P\), divides \(d\). The harmonic sum of this indicator over \(A<d\le z\) is at least \(p_0\ell-2^{\pi(P)}/A\) by partial summation of its divisibility expansion.

For each \(h\), the sum of \(1/d\) over its multiples in \((A,z]\) differs from \(\ell/h\) by at most \(1/A\), by the same partial summation. Remove failures at primes \(p>P\) by union bounds.

* Removing \(p^2\mid d\) costs at most \(y(S\ell+\sqrt z/A)\) in the harmonic main term.
* For \(p^2\mid e,\ P<p\le B_0\), apply the conditioned inner-row estimate. The cost is bounded by \(yS(\ell+1/A)\) plus \(UDB_0\) for each \(d\).
* For \(p\mid(d,e),\ p>P\), apply that estimate for \(p\mid e\) only when \(p\mid d\). Summing \(1/p^2\) and the harmonic discrepancies gives \(y(S\ell+(1+\log z)/A)\) plus \(UD\log z/\log2\) for each \(d\).
* For \(B_0<p\le B,\ p^2\mid e\), both positive weights are at most \(U\) individually. The ordinary count on the row of length \(V=y/d\) is at most \(V/B_0+B\), summing over all integers in the upper bound. For \(p>B\), write \(e=p^2 k\) and sum first over \(k\le z/B^2\). For each \(k\) the real \(p\)-interval has length at most \(V/(2\sqrt{Mk})\). The count of integer \(p\) over these intervals is at most \(V\sqrt{z/M}/B+z/B^2\).

Include the original inner-row discrepancy \(UD\). One obtains the lower bound \((S_0 y-E)/G^2\) for the genuine absolute-weight count, with
\[
 S_0=\ell(p_0-3S)-\frac{2^{\pi(P)}+\sqrt z+1+\log z+S}{A}
 -U^2\left(\frac1{B_0}+\frac{\sqrt{z/M}}B\right)(\ell+1/A),
\]
\[
 E=(z+1)\left[UD(1+B_0+\log z/\log2)+U^2(B+z/B^2)\right].
\]
Dropping the nonsquarefree \(d\) before applying individual row bounds and enlarging only the positive loss terms proves the same inequality even if a row lower bound becomes negative.

## Exact normalization

Write \(g_a(u)=(\cos a-\cos u)/(u^2-a^2)\). On the lobe \(a\le u\le b\), this is the product of \(\operatorname{sinc}((u-a)/2)\) and \(\operatorname{sinc}((u+a)/2)\), divided by two. It is nonnegative and decreasing. Integrate the interval lower bound over superlevels of \(g_a\) on \([K(c-L),b]\), wholly outside the empty interval. Its area \(A_1\) is bounded below by 2048 right-endpoint rectangles, and its peak by \(p_1=\sin(a)/(2a)\). The derivative of physical position with respect to \(u\) is at least \(x/K\). In the normalized physical measure, the remaining weight is bounded below by
\[
 w=(L-b/K)\exp\big((L-c-b/K)/2-(10000b/K)^2\big).
\]
The first-lobe absolute contribution is therefore at least
\[
 \frac{w}{I\,G_+^2}\left(S_0 A_1-\frac Kx E p_1\right),\qquad
 G_+=\log z+1.34+2.44/\sqrt z .
\]
Here \(S_0>.6428058,\ A_1>.4763681\), and the parenthesis is positive. The bound on \(G\) is [Ramaré, Theorem 3.1 and the value of \(c_0\)](https://www.impan.pl/shop/en/publication/transaction/download/product/113104).

For the comparison with the true ordinary near-region main term, put \(r=10^{-6}\). On \(K(c-L)\le |u|\le Kr\), its scalar weight in the \(u\) variable is at least \((L-r)e^{(c-L-r)/2-(10000r)^2}/G_+\). The positive area outside \([-a,a]\), divided by \(I\), is \(1-a/\pi\). At most \(4/[I K r(1-(a/(Kr))^2)]\) is lost to the two tails, by integrating \(2/(u^2-a^2)\), and at most \((K(c-L)-a)/I\) is lost at the inner endpoints. The resulting true ordinary contribution is above .9957931. The same upper and lower calculations require no zero-density estimate or Mertens-function input.

~~~powershell
python -B round8/physical_low/spike_floor.py --lower .0047443
python -B round8/physical_low/spike_floor.py --both --C 4000000 --lower .01433
~~~

The second command integrates both first lobes, which lie in \(q>x/2\). No signed charge is lower-bounded by these estimates. The signed inverse-moment bound for \(q>x\) at the first cutoff is less than .00000607 in [the separate remainder calculation](EMPTY_LCM.md).
