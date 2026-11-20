# A long finite detecting polynomial valid at every high zero in each box

For a [finite rectangle](../kernel/GRID_TARGET.md) use $V=1.01T$, $M=V/4$, $q=128$. Let $u(y)$ be the cumulative distribution function of $M$ plus the sum of $q$ independent uniform random variables on $[0,M/q]$; equivalently it is the integral of a translated $q$-fold convolution of uniform densities. Define
\[
 Z(z)=\sum_{n\le2M}(1-u(n))n^{-z},\quad
 P_X(z)=\sum_{d\le X}\mu(d)d^{-z},\quad D(z)=Z(z)P_X(z)-1
 \qquad (X\le M,\ X\in\mathbb N).
\]
This gives a deterministic finite Dirichlet polynomial. Let $B$ be $D^2$ with all prime-power coefficients removed. For **every** actual zero with $\beta>s,\ H<|\gamma|\le V$, simultaneously within each specified rectangle, the [192-bit certificate](compact_euler.py) gives
\[
\begin{array}{c|cc}
 X & |1+D(\rho)| & \Re B(\rho)\\ \hline
 32768 & <1.728\,10^{-20} & >.9967432\\
 \lfloor V/4\rfloor & <7.299\,10^{-18} & >.9999995389 .
\end{array}
\]
There is no exceptional zero class in this detection statement. Its cost is the length: $B$ has frequencies $X^2<n\le(2MX)^2$, each with at least two distinct prime factors. An upper bound on the count of large values, or a sufficiently small aggregate over the actual zeros, remains necessary. The [shorter Riesz criterion](BILINEAR.md) has a different tradeoff.

## Uniform approximation on the strip

At $z=\sigma+it$ with $s\le\sigma\le7/8$ and $H\le|t|\le V$, apply Euler–Maclaurin to $g(y)=y^{-z}u(y)$ on the positive half-line. Start at $\Re z>1$. The lower boundary derivatives vanish because $u$ is zero through $M$. At infinity the derivatives vanish. The integral of $g^{(q)}$ is zero, so the constant Bernoulli term in the remainder drops out. The remaining periodic Bernoulli polynomial has sup norm divided by $q!$ at most $2\zeta(q)/(2\pi)^q$ by its Fourier series. Both the remainder integral and the expression below for the main integral continue analytically to $\Re z>1-q$, away from the pole at one. Thus
\[
 |\zeta(z)-Z(z)|\le
 \left|\frac{1}{z-1}\int_M^{2M}y^{1-z}u'(y)\,dy\right|
 +\frac{2\zeta(q)}{(2\pi)^q}\int_0^\infty |g^{(q)}(y)|\,dy .
\]
The derivatives through order $q-1$ used here are absolutely continuous on compact intervals as needed, with piecewise derivatives of order $q$. See the [Euler–Maclaurin formula](https://dlmf.nist.gov/2.10.E1) and [periodic Bernoulli Fourier series](https://dlmf.nist.gov/24.8.E1).

For $1\le j\le q$ one has $\|u^{(j)}\|_1\le(2q/M)^{j-1}$: differentiate $j-1$ uniform convolution factors, whose distributional derivatives have total variation $2q/M$, keeping at least one density. The derivatives are supported in $[M,2M]$. In the Leibniz expansion of $g^{(q)}$, the term without a derivative on $u$ costs at most $M^{1-\sigma-q}(|z|+q)^q/(\sigma+q-1)$. The $j$-th remaining term costs at most $M^{1-\sigma-q}\binom qj (|z|+q)^{q-j}(2q)^{j-1}$. As $|z|\le V+1$, the total is bounded by $M^{1-\sigma-q}(V+1+3q)^q$.

Integrate the displayed main integral by parts four further times. The boundary terms vanish, each new denominator has modulus at least $|t|$, and $\|u^{(5)}\|_1\le(2q/M)^4$. Hence
\[
 |\zeta(z)-Z(z)|\le
 \frac{(2M)^{1-s}}{H}\left(\frac{4q}{H}\right)^4+
 2\zeta(q)M^{1-s}\left(\frac{V+1+3q}{2\pi M}\right)^q.
\]
The ratio in parentheses is less than $.637$ in all cases. At a zero multiply this error by $1+(X^{1-s}-1)/(1-s)$, which bounds $|P_X|$ by monotone integration. This proves the first column with no height sampling.

## Coefficients and the prime-power charge

Since $u(n)=0$ for $n\le M$, ordinary Dirichlet inversion gives zero coefficients in $D$ for every $n\le X$, including the constant term. Write $f=1-u$. At a prime power the coefficient before squaring is $f(p^j)-\mathbf1_{p\le X}f(p^{j-1})$ for $j\ge1$. Its modulus is at most one. For $p\le X$ it vanishes as long as $p^j\le M$, so the absolute mass of all powers of that prime in $D$ is at most $M^{-s}/(1-2^{-s})$. For $p>X$ it is at most $p^{-s}/(1-X^{-s})$. Squaring these bounds separately for each prime and summing, the total removed from $D^2$ at any $\sigma\ge s$ is at most
\[
 X M^{-2s}/(1-2^{-s})^2 + X^{1-2s}/[(2s-1)(1-X^{-s})^2].
\]
Finally $\Re D(\rho)^2\ge1-2|1+D(\rho)|-|1+D(\rho)|^2$. All coefficients here are independent of $\rho$. This gives a necessary arithmetic consequence of any failed count. In particular the Landau diagonal $\Lambda(n)$ vanishes at every retained frequency; Landau's sum is over all zeros and does not itself yield the needed upper bound for the selected subset. [Gonek, *A Formula of Landau and Mean Values of ζ(s)*](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf)

~~~sh
python -B round5/spectrum/compact_euler.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. Codex derived the finite uniform estimates above.
