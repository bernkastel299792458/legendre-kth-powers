# A finite signed criterion supported on composite integers with two distinct prime factors

For a count target $K$ at $(s,T)$ from the [thirty rectangles](../kernel/GRID_TARGET.md), use the triangular height weight $W$, $V=1.01T$, and the one-sided limit of the [signed contour criterion](SIGNED_CONTOUR.md). Let $D$ be either the Gaussian tail at $Y=512V$ or the [finite Riesz polynomial](../left/large_values/RIESZ.md) at $Y=cV$. Write
\[
 D(z)^2=\sum_{m>N^2}b(m)m^{-z},\qquad
 B(z)=\sum_{\substack{m>N^2\\m\text{ has at least two distinct prime factors}}}b(m)m^{-z}.
\]
Here $N=32768$. A sufficient condition for a rectangle is
\[
 \liminf_{\eta\downarrow s}\frac1{2\pi}
       \Re\int_0^V W(t) B(\eta+it)\frac{\zeta'}{\zeta}(\eta+it)\,dt
   \ \ge -\kappa K .
\]
For any one row of the table the indicated allowance works simultaneously in all thirty rectangles. It remains open to establish the signed inequality. In the four Riesz cases $b(m)=0$ for $m>Y^2$; no truncation of an infinite Dirichlet expansion is needed.

| Detector | Gaussian $512V$ | Riesz $8V$ | Riesz $32V$ | Riesz $128V$ | Riesz $512V$ |
|---|---:|---:|---:|---:|---:|
| Admissible $\kappa$ | .83408 | .09850 | .37998 | .58287 | .72257 |

**First moment at the zeros.** If the count fails, put $m=N_{>s}(U)>K$ for $T\le U\le V$. At each counted zero write $D(\rho)=-1+e_\rho$. If $\sum|e_\rho|^2/m\le h^2$ and $a=m^{-1}\sum\Re e_\rho$, then $|a|\le h$ and
\[
 \frac1m\sum\Re D(\rho)^2\ge1-2a+2a^2-h^2
 \ \ge 1-2a_*+2a_*^2-h^2,\quad a_*=\min(h,1/2).
\]
The first inequality uses Jensen on the real part, retaining the favorable real square. This permits the $8V$ row. For the Gaussian use the critical expense from the [quadratic contour](../left/large_values/QUADRATIC_CONTOUR.md), with the indicated $10^{-28}$ allowance per zero. For Riesz recover the squared near-integral bound from the paired Poisson row at $(s,V,Y)$ by multiplying its count expression by $(1/2-10^{-4})^2$. Divide by $K$ and take the square root. Add separately the far-integral upper bound from the Riesz proof, evaluated at the actual $s,V,Y$, and the Mellin residual $Y^{-3/4}+210N(3/4)Y^{1-s}/H^2$. This bounds $h$ by the triangle inequality for the vector of all $m$ errors. The near-integral calculation itself is independent of the tail scale, so this also applies at $8V$.

**Removing the prime powers.** For every prime $p\le N$ the coefficient $a(p^j)$ of $\zeta P$ vanishes for all $j\ge1$, by the terms at $1$ and $p$ of the sharp mollifier. For $p>N$ it equals one. Both smoothing weights lie in $[0,1]$. Thus $|b(p^j)|\le j-1$ for $j\ge2$ and $b(p)=0$. On any line of real part at least $s$ the discarded coefficients have total absolute mass at most
\[
 M_s=(1-N^{-s})^{-2}N^{1-2s}/(2s-1)
\]
by summing the geometric derivative at each prime and bounding its tail by the integral over all integers. Subtract $M_s$ from the lower average at the zeros. No frequency with $\Lambda(m)\ne0$ survives in $B$. A product $\ell p$ of two primes with $\ell\le N<p$ also has coefficient zero because each of the two Dirichlet factors starts strictly after $N$. This removes the specific prime and small-cofactor semiprime coefficients used in the [independent-block tests](../left/large_values/SEMIPRIMES.md). It supplies no sign estimate on the remaining coefficients.

**Contour charges.** Apply the contour identity to $-B$ to get the displayed *lower* bound as the sufficient condition. For the Gaussian square its horizontal, pole and right-edge charges are bounded by the positive charges for $2D+D^2$ in the quadratic contour proof. That proof adds the contributions of $2D$ and $D^2$ in absolute value when estimating the edges; the bound $10/(2\pi\log N)$ on the right also suffices for $D^2$ alone by absolute convolution and $\log(mn)\ge2\log N$ for the two tail factors. For Riesz the same horizontal second-moment formula applies: for each $\alpha>0$ the squared finite weight is at most $(Y/n)^\alpha$, so the Gaussian upper bounds used there apply as written. The squared-polynomial horizontal estimate uses the regular and near-zero summands in [the quadratic proof](../left/large_values/QUADRATIC_CONTOUR.md).

To bound the Riesz pole value, shift the Mellin kernel $\lambda/[w(w+\lambda)]$, $\lambda=3/4$, at $z=1$ to $\Re w=-1/2$. Its double-pole residue in the product is $P'(1)+P(1)(\log Y+\gamma_E-1/\lambda)$. Subtract $1-Y^{-\lambda}$. The remaining integral has modulus at most $6\cdot431\cdot15\sqrt2/(2\pi\sqrt Y)$: use $|\zeta(1/2+iv)|\le6\sqrt{1+|v|}$ and $|P|\le431$. The integral of $\sqrt{1+|v|}|K(-1/2+iv)|$ is at most $12\sqrt2$ on $|v|\le1$ and $3\sqrt2$ outside. This gives the pole charge $|D(1)|^2/2$ with $P(1),P'(1)$ evaluated as in the quadratic proof.

Finally add charges for the removed prime powers. Write $G=3+[2(2-s)+2.5]A$ for the regular bound and $J$ for the near-logarithm root mean square in [the linear proof](SIGNED_CONTOUR.md). The added horizontal, pole and right-edge costs together are at most $M_s[((2-s)G+J)/(2\pi)+1/2+1/(2\pi\log N)]$. On the right use absolute convergence, $-\zeta'(2)/\zeta(2)<1$ and the minimum frequency. All allowances are computed at each actual rectangle. The remaining low frequencies have no von Mangoldt diagonal, but controlling the signed expression for the selected high-real-part zeros remains necessary.

~~~sh
python -B round5/spectrum/bilinear_contour.py
~~~

The [192-bit verifier](bilinear_contour.py) reproduces the table.

**A test of removing the first prime frequencies by moments.** Write $A(z)=\sum_{N<p\le b}c_pp^{-z}$, with $|c_p|\le1$. On disks of radius $r=1/(k\log N)$ about the counted zeros use the submean inequality for $|A|^{2k}$. At a given ordinate $u$ at most $A_0/L$ disks overlap, where $A_0=\tfrac12\log(2T)+3$ and $L=1/(2-s+r^2/(2-7/8))+1/(1+7/8+r^2/(1+s))$. This follows from the Poisson bound at 2 and the two zeros of each reflected pair. Put $x=s-r$, $q_i=\sum_{N<p\le b}p^{i-2x}$ and $l=V-H+2r$. Unique factorization bounds the two coefficient energies of $A^k$ by $k!q_0^k,k!q_1^k$: any ordered tuple of primes has at most $k!$ permutations with that product. The time mean theorem and integration in the real part, as in the linear contour proof, yield
\[
 \sum_{\rho}|A(\rho)|^{2k}\le \frac{A_0 k![(l+5)q_0^k+10q_1^k]}{2\pi Lr^2 k\log N}.
\]
The sum counts $H<\gamma\le V,\beta>s$. For a set of $m>K$ such zeros, divide by $K$ and take the $2k$-th root to bound its root mean square. The [prime-block test](prime_block.py) minimizes this expression over $k=2,\ldots,9$, using exact prime counts in intervals of 32 and left-edge powers. On the bands with $b=N+2048,N+4096,N+8192$, this computed bound is greater than $1.61$ times even the corresponding elementary upper bound $\sum p^{-s}$ using the same bins, in every rectangle. At $b=2N$ the best ratio among all rectangles is $.911706$ to six decimals. This quantifies the limited saving from the tested moment formula for these bands; sharper estimates could behave differently.

Joint project attribution to Claude and Codex. Codex derived this finite bilinear criterion on 2026-11-20.
