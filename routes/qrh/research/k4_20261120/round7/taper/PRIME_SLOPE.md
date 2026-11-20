# Prime coefficients in the remote part of the Gram bound

At frequencies \(n/T\) greater than the chosen cutoff the [local mean bound](../../round5/mean/RIGHT.md) continues with the same linear coefficient \(C\pi\lambda_j/Q\) throughout, where \(j=\lfloor S/\mathrm{cutoff}\rfloor+1,\ S=Qva(1+\epsilon_0)e^{\epsilon_0^3}/\pi\). Here \(j\) may be rounded up by interval arithmetic and \(\lambda_j\) denotes its certified Gram upper bound. On the part \(V\le vaT\) of the auxiliary probability measure used there, the actual number of Fourier samples for \(n/T\ge z_i=S/i+.01\) is at most \(i\), provided \(z_i\) is also at least the cutoff. Its linear coefficient is then at most \(C\pi\lambda_i/Q\). The exceptional probability is at most \(2a^{-2048}\), since the already used first-moment tail is at most \(vT(2048/2047)a^{1-2048}\). Keep the old upper bound on that exceptional set and on all the nonprime coefficients.

At a prime \(p>Y\) not dividing \(Q\), the Dirichlet coefficient of the same detector is \(1-\omega(p)\); it reaches 1 at \(X=Y e^W\). For a fixed slab \(U\le\log T\le V_0\) and every \(p>P=e^{V_0}z_i\) its coefficient is at least \(\min(1,\max(0,\log(z_i/h)/W))\). With \(e_*=2\delta/U\), partial summation gives
\[
 \sum_{p>P}p^{-1-e_*}\ge(1+e_*)E_1(e_*\log P)
                -1.25506\,P^{-e_*}/\log P.
\]
Here \(E_1(x)=\int_x^\infty e^{-v}dv/v\). Use the lower \(\pi(t)>t/\log t\) in the integral and the upper \(\pi(P)<1.25506 P/\log P\) in the endpoint term, valid since \(P>17\). [Rosser–Schoenfeld, equations (3.5)–(3.6)](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)

Descending in \(i\) from \(j-1\) to 1, replace each \(\lambda_i\) by its minimum with the preceding upper bound and credit only the difference in these two slopes. The sets \(p>P\) are nested, so their cumulative credits telescope within the same original linear term. Divide by \(V_0\) to bound the deduction after the normalization by \(\log T\); the factor \(Y^{-e}\) cancels. All terms concern the true coefficients in the exact norm and can therefore be deducted after a separate arithmetic upper bound on that norm has been applied. With \(U=37,V_0=37.125,W=9.5,\delta=1.16,\log h=-3\) and cutoff 160 the absolute saving in the normalized right mean exceeds \(1.2375\cdot10^{-6}\).

~~~sh
python -B round7/taper/prime_slope.py
~~~

## Two and three distinct prime factors

For each product \(n\) of two or three distinct primes coprime to \(Q\), the same Gram slope applies to the actual coefficient \(c_n=\sum_{d\mid n}\mu(d)\omega(d)\). Write \(y=\log Y\), with \(W\omega(d)=\min(W,\max(0,y+W-\log d))\). Use the alternating sum over all subsets of those prime factors. On logarithmic prime cells of width \(1/4\), each endpoint and \(y\) is bounded outwards in integer ticks of \(1/3200\). For a subset of size \(h\) the spread in the sum of log primes is \(h/4\). Use the lower positive distance between the resulting coefficient interval and zero. Every retained prime exceeds \(e^7\), so all are units modulo 2310.

For \(e_*\ge2\delta/U\) the harmonic prime mass on \(a<\log p\le b\) is at least
\[
 S=\frac{e^{-(1+e_*)b}}b\left[e^b-e^a-\frac{a^2e^{a/2}+b^2e^{b/2}}{8\pi}\right]_+ .
\]
This uses the two endpoint bounds for \(\vartheta\) on the full published range \(599\le x\le2.169\cdot10^{25}\). Use only bins inside \([7,56]\). If two or three primes occupy the same bin, they must be distinct. With \(M=e^{-(1+e_*)a}\), their elementary symmetric masses are at least \(S(S-M)_+/2\) and \(S(S-M)_+(S-2M)_+/6\). This follows by adding a further distinct prime to each term and dividing by the number of choices for the last prime. Weight all products by the lower endpoint of \(|c_n|^2\), and admit a bin only when the sum of its lower log endpoints exceeds \(V+\log z_i\). The resulting sums for nested Gram improvements are disjoint from the existing prime credit. [Johnston, Corollary 3.3 and finite-height estimates](https://link.springer.com/article/10.1007/s11139-022-00616-x)

The [product calculation](product_slope.py) rounds each single-bin mass downwards, then enlarges the total downward error by a factor \(1-2\cdot10^{-8}\). There are fewer than \(\binom{258}{3}+\binom{257}{2}\) positive terms, fewer than 900 further cumulative additions, and fewer than 20 binary64 rounding factors in each individual positive product. The integral inputs, ratios outside the finite sum, and final interval comparisons use Arb. At \(U=34,37,40\), \(V=U+1/16,\delta=1.16,W=9,\log h=-3\), cutoff 320, the normalized extra deductions exceed \(1.19360,1.23828,1.27106\) in units of \(10^{-6}\).

~~~powershell
python -B round7/taper/product_slope.py
~~~
