# A location-sensitive Selberg bound for the physical intervals

Let \(M,y\) be positive reals. Uniformly when
\[
 e^{114.98}\le M<M+y\le e^{115.12},\qquad e^{83}\le y\le e^{89},
\]
one has
\[
             \pi(M+y)-\pi(M)\ \le\ \frac{2y}{\log y+2.10}.                  \tag{1}
\]
The proof is unconditional. The finite frequency calculations exploit both the location and the length of the interval. They give the denominator additions in the table; the indicated bound applies to every real \(y\) in its closed cell.

| \(\log y\) | Upper \(E\) for the remainder divided by \(y\) | Denominator addition exceeds |
|---|---:|---:|
| 83 to 84 | .000133491 | 2.16072 |
| 84 to 85 | .000092630 | 2.30609 |
| 85 to 86 | .000072263 | 2.37797 |
| 86 to 87 | .000063438 | 2.40700 |
| 87 to 88 | .000061969 | 2.40732 |
| 88 to 89 | .000066532 | 2.38250 |

## Finite Selberg identity

Set \(z=\sqrt y\),
\[
 G=\sum_{k\le z}\frac{\mu^2(k)}{\varphi(k)},\qquad
 G_d(v)=\sum_{k\le v,(k,d)=1}\frac{\mu^2(k)}{\varphi(k)},\qquad
 \lambda_d=\frac{\mu(d)d}{\varphi(d)G}G_d(z/d)\quad(d\le z).
\]
Then \(\lambda_1=1\) and \(\sum_{d,e\le z}\lambda_d\lambda_e/[d,e]=1/G\). For example, write this last quadratic form as \(\sum_r\varphi(r)(\sum_{r\mid d}\lambda_d/d)^2\); divisor inversion gives the inner sum \(\mu(r)/(\varphi(r)G)\) for squarefree \(r\le z\) and zero otherwise. Each prime in the interval exceeds \(z\), so its Selberg square is 1; all other squares are nonnegative. Counting multiples gives the upper bound \(y/G+\mathcal E\) with
\[
 \mathcal E=\sum_{d,e\le z}\lambda_d\lambda_e
 \left(\{M/[d,e]\}-\{(M+y)/[d,e]\}\right).
\]
These identities include integral endpoints with the half-open convention of (1). [Selberg weights, equations (3)–(4)](https://www.math.columbia.edu/~goldfeld/Brun-Titchmarsh.pdf)

For squarefree \(d\), multiplying \(G_d(z/d)\) by \(d/\varphi(d)=\sum_{r\mid d}1/\varphi(r)\) only uses distinct terms of \(G\). Thus \(|\lambda_d|\le1\). Also
\[
 G\sum_{d\le z}|\lambda_d|
  =\sum_{k\le z}\frac{\mu^2(k)\sigma(k)}{\varphi(k)}
  \le zK,\qquad
 K=\prod_{p\le1000}\left(1+\frac2{p(p-1)}\right)e^{2/1000}.
\]
For this inequality expand \(\prod_{p\mid k}(1+2/(p-1))\) and drop squarefreeness in its sum. The remaining Euler-product logarithm is bounded by \(\sum_{n>1000}2/(n(n-1))=2/1000\). In a block \(z/2^{i+1}<d\le z/2^i\), use \(|\lambda_d|\le L_i=\min(1,\rho G(2^{i+1})/G)\), where \(\rho\) is the product of \(p/(p-1)\) over the longest prime initial segment whose primorial is at most the largest \(z\) in the cell. The prefix for \(2^{i+1}\le256\) is exact. Else use \(G(v)\le\log v+2+2.44/\sqrt v\). The same published estimate gives \(G\ge\log z+1.331\) throughout. [Ramaré, Theorems 1.3 and 3.1](https://www.impan.pl/shop/en/publication/transaction/download/product/113104)

## Vaaler and the nonzero Fourier sums

Write \(e(t)=e^{2\pi it}\) and \(J=128\). Vaaler's degree-\(J\) approximation to the centered sawtooth has nonzero coefficient modulus at most \(1/(2\pi|n|)\). The absolute pointwise error is at most the order-\((J+1)\) Fejér kernel divided by \(2(J+1)\). The latter also majorizes the choice \(\{x\}-1/2=-1/2\) at integers. If \(B_n\) bounds, after division by \(z^2\), every sum
\[
 \left|\sum_{d,e\le z}v_d v_e\, e(nt/[d,e])\right|,
 \qquad t\in\{M,M+y\},\quad v=\lambda\text{ or }|\lambda|,
\]
then
\[
 \frac{|\mathcal E|}{y}\le
 \frac{(K/G)^2}{J+1}+
 \sum_{n=1}^J\left(\frac{2}{\pi n}+\frac{2}{J+1}\right) B_n .              \tag{2}
\]
Both endpoints, both frequency signs, and the nonnegative Fejér error have been charged here. The coefficient weight in Vaaler's formula is between zero and one. [Vaaler, Theorem 18](https://doi.org/10.1090/S0273-0979-1985-15349-2)

Set \(g=(d,e)\) and use \(\mathbf1_{(d/g,e/g)=1}=\sum_{h\mid(d/g,e/g)}\mu(h)\). In the resulting sums \(d=gh x,e=gh w\), and the original phase is \(e(A/(xw))\), \(A=nt/(gh^2)\), because the coprime version of the original denominator is \(g(d/g)(e/g)\). The individual coefficient bounds remain valid and the two variables are now separate. Discard \(g>G_*=2^{24}\) **before** inversion with cost at most \(z^2/G_*\); after inversion \(h>G_*\) costs at most \(z^2\zeta(2)/G_*\). Retain the first \(m=30\) dyadic blocks in each original variable; discarded pairs after inversion cost at most \(2z^2\zeta(2)^2/2^m\). These tails are charged in **each** \(B_n\) in (2).

## Bilinear bound with arbitrary separated coefficients

Suppose \(x\in(D/2,D],w\in(F/2,F]\), \(D\ge F\) by symmetry. Let \(d_0=\min(1,1/2+1/D)\), \(e_0=\min(1,1/2+1/F)\). Thus \(N_x\le d_0 D,\ N_w\le e_0 F\), including nonintegral endpoints. If both sequences of coefficients are bounded by one, the sum \(S\) of their products times \(e(A/(xw))\) satisfies
\[
 \frac{|S|}{DF}\le\min\left(d_0e_0,\sqrt{d_0e_0\left[
     d_0/F+32d_0e_0A/(D^2F^2)+4LDF/A+128Le_0/D\right]}\right),
 \quad L=1+\log z.                                                        \tag{3}
\]
To see this, split the consecutive \(w\)-indices into runs of length \(\lfloor D^2F^2/(32A)\rfloor+1\). There are at most \(1+32A e_0 F/(D^2F^2)\) runs. Cauchy in \(x\) and in the run label gives \(N_x\) times this number times the sum of all unweighted \(x\)-square sums within runs. For one pair \(w,w'\) of positive difference \(r\) in a run, the absolute derivative of their difference phase is \(Ar/(x^2ww')\), monotone in \(x\) and between \(Ar/(D^2F^2)\) and \(1/2\). The first-derivative sum on the entire \(x\)-block is therefore bounded by \(2D^2F^2/(Ar)\). This generous constant follows, for instance, from the Kusmin–Landau cotangent bound (the assertion for a singleton follows directly). There are at most \(N_w\) pairs for each \(r\) and two signs; \(\sum_{r\le z}1/r\le L\). Thus the square sums are bounded by \(N_w[N_x+4D^2F^2L/A]\). Expanding and dividing by \(D^2F^2\) proves (3). If a block is empty its contribution is zero. [Kusmin–Landau inequality, Theorem 17.3](https://websites.umich.edu/~hlm/math775/ch17.pdf)

For dyadic indices \(i\ge j\), use \(D=z/(gh2^j)\), \(F=z/(gh2^i)\). Its contribution to \(B_n\) is the right side of (3) times \(L_iL_j2^{-i-j}/(gh)^2\), doubled when \(i\ne j\). For a frequency group \(n_0\le n\le n_1\), the term involving \(A/(D^2F^2)\) is bounded by \(n_1 e^{115.12}g^3h^2 2^{2(i+j)}/z_{\min}^4\); \(DF/A\) is at most \(z_{\max}^2/(e^{114.98}n_0 g 2^{i+j})\). Use the smallest possible dimensions in the other terms, and the largest \(L\). Group each of \(g,h\) by singletons through 31 and then doubling ranges \([a,b]\); its factor \(\sum r^{-2}\) is at most \(1/a^2+1/a-1/b\). The code adds the tails before multiplying by the Fourier coefficient bound in (2).

## Directed finite evaluation

The v-dependent and primal constants, including the six actual logarithmic length boxes, use 192-bit Arb. The inputs to the positive binary64 array kernel are rounded from Arb upper or lower endpoints with an extra factor \(1\pm2^{-48}\) on the indicated side. All integer indices, group endpoints and powers of 2 in the finite ranges are exact as binary64 values. The inner loop contains only positive products, quotients, sums, square root and minimum, without fast-math. The maximum cumulative operation count is checked below \(2^{22}\). More explicitly, the relative losses of a single term are less than \(200\cdot2^{-52}\): forming a dimension involves at most three multiplications and a quotient; the unreduced expressions use at most four powers of any input, the two powers of dimensions have already been expanded in (3), and the square root and minima do not increase the maximum relative input error. A sum of positive terms loses at most another factor \((1-2^{-52})^{2^{22}}\). All positive intermediates lie between \(10^{-150}\) and \(10^{180}\), as follows from \(g,h\le 2^{24}\), \(i,j\le29\), \(1\le n\le128\), \(e^{41.5}\le z\le e^{44.5}\), and the displayed powers. Thus every ordinary rounding is on normal binary64 numbers. Returning to Arb and multiplying by \(1+10^{-7}\) safely encloses these losses. No signed floating-point cancellation occurs. The clustering of \(g,h,n\) only enlarges the bounds.

For a length box \(l\le\log y\le u\), the output \(E\) from (2) gives
\[
  \pi(M+y)-\pi(M)\le y\,[1/(\tfrac12\log y+1.331)+E].
\]
Consequently the additive denominator exceeds \(2(1.331)-2E(u/2+1.331)^2\). Every row verifies that expression strictly above 2.10. The sharper row-wise bounds are also retained in the table. [Replay the six boxes](bilinear.py)

~~~powershell
python -B round7/physical/bilinear.py
~~~
