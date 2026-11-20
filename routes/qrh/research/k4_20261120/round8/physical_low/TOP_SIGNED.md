# Signed low-frequency Selberg weights on the actual coprime top row

Fix \(L=116,\ H=3000175332800,\ x=e^L,\ z=3000000\sqrt{x/H}\). For \(e^{-2\cdot10^{-6}}x\le t\le e^{2\cdot10^{-6}}x\), the following signed bounds hold for the real top row including all coprimality restrictions
\[
 T_r(n,t)=\frac1{z^2}\sum_{\substack{z/2<d,e\le z\\(d,e)=1}}
   \lambda_d\lambda_e (z/d)^r(z/e)^r
                 \exp(2\pi i n t/(de)).
\]
The closed upper bounds for \(|T_1|\) at \(n=1,2,4,8\) are respectively \(1.75635\,10^{-7},5.29262\,10^{-7},1.81997\,10^{-6},6.73518\,10^{-6}\). The corresponding sum of absolute amplitudes exceeds \(1.49108\,10^{-5}\). The first Fourier coefficient thus admits a factor greater than 84 from genuine coefficient cancellation. The method uses the ordinary real Mertens sum and finite-dimensional estimates, without a contour shift.

## Exact complete moments

Set
\(G=\sum_{m\le z}\mu^2(m)/\varphi(m)\) and \(G_d(y)=\sum_{m\le y,(m,d)=1}\mu^2(m)/\varphi(m)\).
For the [original Selberg weights](../../round7/physical/BILINEAR.md), the identity
\(G\lambda_d=\mu(d)d\sum_{u\le z,d\mid u}\mu^2(u)/\varphi(u)\)
follows by substituting \(u=dm\). If \(k\le z\) is squarefree and \(s\) is real, divisor inversion gives
\[
 G\sum_{k\mid d}\lambda_d d^{-s}=
 \frac{\mu(k)k^{1-s}}{\varphi(k)}
 \sum_{\substack{m\le z/k\\(m,k)=1}}
 \frac{\mu^2(m)}{\varphi(m)}
          \prod_{p\mid m}(1-p^{1-s}).                                  \tag{1}
\]
Indeed the sum of \(\mu(d)d^{1-s}\) over \(k\mid d\mid km\) factors prime by prime. At \(s=0\) the last sum equals \(\sum_{m\le z/k,(m,k)=1}\mu(m)\). At \(s=1\) only \(m=1\) contributes, and at \(s>1\) it is nonnegative. Thus the complete order-zero double moment is \((M(z)/G)^2\). For \(s>0\) the complete inverse lcm moment is nonnegative because
\[
 \sum_{d,e}\lambda_d\lambda_e[d,e]^{-s}
  =\sum_{k\le z}J_s(k)\left(\sum_{k\mid d}\lambda_d d^{-s}\right)^2,
 \qquad J_s(k)=k^s\prod_{p\mid k}(1-p^{-s}).
\]
One cannot apply these complete identities unchanged after truncating the lcm. The next calculation instead evaluates a genuine frequency subregion.

## Real Möbius cancellation throughout the top row

Write \(\rho(q)=q/\varphi(q)\). On this row \(G_d(z/d)=1\) exactly. Remove \((d,e)=1\) by \(\sum_{h\mid(d,e)}\mu(h)\). Write \(d=hu,e=hv,D=z/h\). On a nonzero row \(\mu(h)^2=1,\ (u,h)=1\). Both one-variable rows then have the signed coefficients \(\mu(h)\rho(h)\mu(u)\rho(u){\bf1}_{(u,h)=1}/G\).

Let \(C_h(y)=\sum_{u\le y,(u,h)=1}\mu(u)\rho(u)\). The coefficient is \(\mu*c_h\), where for every prime power \(p^a,\ a\ge1\), \(c_h(p^a)=-1/(p-1)\) if \(p\nmid h\), and \(c_h(p^a)=1\) otherwise. This follows by formal multiplication of the local series by \(1-X\). For \(s>0\) its absolute coefficient moment is
\[
 \sum_{a\ge1}|c_h(a)|a^{-s}=C_s\prod_{p\mid h}r_s(p),\quad
 C_s=\prod_p\left(1+\frac1{(p-1)(p^s-1)}\right),\quad
 r_s(p)=(1-p^{-s}+p^{-s}/(p-1))^{-1}.
\]
Take \(J=10^7,\ B=e^{21},\ Y=z/(2J)\). For \(h\le J,\ y\in[z/(2h),z/h]\), bound \(M(y/a)\) in the convolution by \(.006688(y/a)/\log B\) when \(a\le y/B\) and by \(y/a\) afterwards. The latter part uses \(1/a\le (B/Y)^{1/2}/\sqrt a\). The published bound holds whenever \(y/a\ge B>1798118\). [Ramaré and Zuniga Alterman, *From explicit estimates for the primes to explicit estimates for the Möbius function II*, Theorem 1.1](https://arxiv.org/abs/2408.05969)

Writing \(|C_h(y)|\le y\epsilon_h\), the weighted square norm obeys by Minkowski
\[
 V=\left(\sum_{h\le J}\frac{\mu^2(h)\rho(h)^2}{h^2}\epsilon_h^2\right)^{1/2}
 \le \frac{.006688}{\log B}C_1P_1^{1/2}
       +\sqrt{B/Y}\,C_{1/2}P_{1/2}^{1/2},\quad
 P_s=\prod_p(1+(r_s(p)/(p-1))^2).
\]
For each \(C_s\) the product over \(p>Q=2000\) has logarithm at most \(Q^{-s}/[s(1-1/Q)(1-Q^{-s})]\), by replacing primes with all integers. For \(P_s\) the same tail has logarithm at most \(1/[Q(1-1/Q)^2(1-Q^{-s})^2]\). The [scalar verifier](top_signed.py) gives \(V<.002207\).

On \(D/2<u\le D\), partial summation shows the cumulative sum with multiplier \((D/u)^r\) is at most \(D b_r\epsilon_h\) in modulus, \(b_0=3/2,\ b_1=2+\log2\). For \(u/D,v/D\in[1/2,1]\) the kernel is \(f(X,Y)=\exp(2\pi i nt/(z^2XY))\). Put \(\omega=2\pi nt/z^2\). Double Abel summation bounds its total multiplier by
\[
  |f(1,1)|+\int_{1/2}^1 (|f_X(X,1)|+|f_Y(1,X)|)\,dX+
                      \int_{[1/2,1]^2}|f_{XY}|
       \le 1+3\omega+\tfrac94\omega^2.
\]
In the last estimate use \(\int_{1/2}^1 X^{-2}dX=1\), \(\int_{1/2}^1 X^{-3}dX=3/2\). For \(h>J\), bound \(\rho(d)\) by \(R\), the product of \(p/(p-1)\) over the longest prime prefix with primorial at most \(z\), count at most \((z/h)^2\) pairs and use \(\sum_{h>J}h^{-2}\le1/J\). Thus
\[
 |T_r(n,t)|\le
 \frac{ b_r^2 V^2 (1+3\pi nt/z^2)^2+2^{2r}R^2/J}
      {(\log z+1.331)^2}.                                                \tag{2}
\]
The lower bound for \(G\) is checked as in the original sieve proof.

For the comparison with the absolute sum, put \(b=z/2\). Imposing squarefreeness and mutual coprimality at \(p=2,3,5,7\) on the two coordinates retains at least \((b-210^2)^2\prod_{p\mid210}(1-1/p)^2(1+2/p)\) pairs by the Chinese remainder theorem modulo \(210^2\). For primes \(p>7\) put \(U=\sum_{p>7}p^{-2}\), bounded by the prefix through 1000 plus \(1/1000\). At most \(2(b+1)(bU+\sqrt z)\) pairs have a remaining squared prime factor in one coordinate. At most \(b^2U+2b(1+\log z)+z\) pairs have a remaining common prime, by squaring \(b/p+1\) and summing. All surviving absolute normalized amplitudes are at least \(1/[z^2(\log z+2+2.44/\sqrt z)^2]\). This proves the stated lower bound without a prime-distribution asymptotic.

For the two first Logan lobes at \(L=116,K=H\), retaining just this coprime top row in the signed endpoint difference, the sum of the first four nonzero harmonic costs is below **.000387424**. In fact the [integrated physical cost](../../round7/physical/WEIGHTED_LOBE.md) multiplies each \(|T_1(n,t)|\) by at most \(4(c+r_0)e^{3r_0/2+c-L}A_1/I\), \(r_0=10^{-6}\). This is the low-frequency integration-by-parts scale including both Fourier signs and the two reflected lobes. Enclose \(A_1\) by 1024 trapezoids with the inherited \(|g''|\le1/12\). Other harmonics, dyadic rows, noncoprime pairs and the rest of the physical budget remain outside this bound.

~~~powershell
python -B round8/physical_low/top_signed.py
~~~
