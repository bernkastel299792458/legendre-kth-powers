# A signed vertical integral for each finite rectangle

Use the thirty $(s,T)$ of the [finite reduction](../kernel/GRID_TARGET.md), and put $K=6\log(T)T^{3(1-s)/(3s-1)}$, $\Delta=T/100$, $V=T+\Delta$, $Y=512V$. Use $D_Y(z)$ from the [Gaussian detector](../left/large_values/GAUSSIAN.md). Set $W(t)=1$ on $[0,T]$, $(V-t)/\Delta$ on $[T,V]$ and zero above $V$. The following thirty inequalities **would suffice** for the entire fourth-power gap:
\[
 \limsup_{\eta\downarrow s}\frac1{2\pi}\Re\int_0^V
     W(t)D_Y(\eta+it)\frac{\zeta'}{\zeta}(\eta+it)\,dt
       \ \le\ .91646 K .
\]
Take $\eta>s$ avoiding real parts of zeros up to height $V$. The remaining integrals have explicit weights and one-sided signs. Their upper bounds are open. All numerical statements below concern the proved allowances for the other terms. The assumptions of the Gaussian detector, including QRH(7/8) and verified RH to $H$, remain in effect.

## From detection to a first moment

Suppose $N_{>s}(T)>K$. For any $T\le U\le V$ outside zero ordinates let $m=N_{>s}(U)>K$. The Mellin identity in the Gaussian proof gives $|1+D_Y(\rho)-I_{\rho,\mathrm{near}}|<10^{-28}$ at every counted zero. The [reflected sampling inequality](REFLECTION.md) bounds $\sum_{\gamma\le U}|I_{\rho,\mathrm{near}}|^2$ over the counted zeros by $B_2$. At $(s,V,Y)$, the script takes the single-height reflected Type II count bound and multiplies it back by $(1/2-10^{-40})^2$ to recover this squared-norm bound. Write $h=\sqrt{B_2/K}$. By Cauchy,
\[
 -\Re\sum_{\rho}D_Y(\rho)\ge (1-10^{-28})m-\sqrt{m B_2}
   \ge (1-10^{-28}-h)K .
\]
Here the coefficient on the right is positive. The inequality holds for each $U$, including when the count changes with $U$.

## A rectangle with an averaged top

Let $F=D_Y\,\zeta'/\zeta$. Integrate $F$ counterclockwise on $[\eta,2]+i[-U,U]$. For all sufficiently small $\eta-s>0$ the right-hand zeros in this rectangle are independent of $\eta$, since there are finitely many zeros up to $V$. The log derivative has residue $-1$ at $1$. The residues therefore total $2\Re\sum_\rho D_Y(\rho)-D_Y(1)$. The contribution of the left edge to $-\Re\sum D_Y(\rho)$ is $(2\pi)^{-1}\Re\int_0^U F(\eta+it)dt$. The right edge has the opposite sign and the same normalization. The absolute charge for both horizontal edges after division by two is at most $(2\pi)^{-1}\int_\eta^2 |F(x+iU)|dx$.

The coefficients $a(n)$ in $D_Y$ vanish through $N=32768$ in this tail and satisfy $|a(n)|\le d(n)$, since the sharp short polynomial has coefficients $0,\pm1$. On the right, integrate the cosine at frequency $\log(nm)$ after using the absolutely convergent log derivative series. Its absolute integral is at most $1/\log N$, uniformly in $U$. The right edge thus costs at most $4/(2\pi\log N)$, using $\zeta(2)<2$ and $-\zeta'(2)/\zeta(2)<1$. For the latter comparison one may use $\sum_{n\ge2}(\log n)/n^2\le(\log2)/4+\int_2^\infty(\log t)/t^2dt$ and $\zeta(2)>1+1/4$. With $b=\sqrt2(3/8)$ and $\epsilon=1/\log Y$, the normal distribution satisfies $\Phi(b\log(Y/n))\le(Y/n)^\epsilon e^{\epsilon^2/(2b^2)}$. Absolute convolution with the short polynomial, supported up to $210N$, gives the pole charge
\[
 \tfrac12|D_Y(1)|\le\tfrac12 e^{1+\epsilon^2/(2b^2)}
     (1+1/\epsilon)(1+\log(210N)).
\]

## Bound for the two horizontal edges together

Write $A=\tfrac12\log(2T)+3$, $P_a(v)=a/(a^2+v^2)$. For $T-2\le u\le V+2$, the log derivative identity used in the Gaussian proof gives $\sum_\rho P_{2-\beta}(u-\gamma)\le A$, summing over **all** nontrivial zeros with multiplicity. Indeed $\Re\psi(1+iy)=-\gamma_E+\sum_{n\ge1}y^2/[n(n^2+y^2)]\le2+\log y$ here by splitting at $\lfloor y\rfloor$, and the pole terms at $2+iu$ are smaller than $1$. Therefore each $u$ has at most $2.5A$ zeros within unit distance in ordinate, since $P_{2-\beta}\ge2/5$ there. There are at most $(\Delta+4)A/.9$ ordinates in $[T-1,V+1]$. To see this integrate the kernel sum on $[T-2,V+2]$ and use $2\arctan(1/2)>.9$ for each such zero.

For $s\le x\le2$ subtract the log derivatives of the completed zeta function at $x+iu,2+iu$ using its Hadamard product. Each zero with $|u-\gamma|>1$ costs at most $2(2-s)P_{2-\beta}(u-\gamma)$, by taking the absolute difference of the two reciprocal factors. For a near zero keep $1/|x+iu-\rho|$ and bound its reference reciprocal by $1$. The remaining regular terms, including $|\zeta'/\zeta(2+iu)|$, cost at most $3$. For the gamma difference use $\psi'(w)=\sum_{n\ge0}(w+n)^{-2}$ and $\sum_{n\ge0}((\Re w+n)^2+y^2)^{-1}\le y^{-2}+\pi/(2y)$ for $\Re w>0$. The two rational terms in the completed derivative have differences less than $1$ in total here. The resulting regular bound is $3+[2(2-s)+2.5]A$.

For a near zero, integrating its reciprocal over $x\in[s,2]$ costs at most $2\log(4/|u-\gamma|)$ when $0<|u-\gamma|\le1$ (integrate from the closest point on either side, each side of length at most $1.2$). The sum of these logarithms, including the factor $2$, has root mean square over $u\in[T,V]$ at most
\[
 A\sqrt{\frac{2.5(\Delta+4)}{.9\Delta}
       8\big[(\log 4)^2+2\log4+2\big]} .
\]
This follows from Cauchy at each $u$, the two zero counts just proved and integration of $\log^2(4/|v|)$ on $[-1,1]$. Thus the full uniform average in $U$ exists across zero ordinates.

For any interval of length $l$ let $B(q,l)$ bound the average $|D_Y(q+it)|^2$. The explicit complex-coefficient mean theorem used in the [frozen fourth-moment proof](../low/FROZEN_FOURTH.md) gives this upper bound, for any $0<e<2q-1$ and $\alpha=2-2q+e>0$ used in the script:
\[
 (1+5/l)\min\{\zeta(2q)^4,N^{-(2q-1-e)}\zeta(1+e)^4\}
  + (10/l)e^{\alpha^2/(4b^2)} Y^\alpha \zeta(1+e)^4 .
\]
Use $d(n)^2\le d_4(n)$, the divisor function of order four, and the squared Gaussian tail bound $\Phi^2\le(Y/n)^\alpha e^{\alpha^2/(4b^2)}$. Absolute convergence permits truncation and passage to the limit. Each summand can be minimized separately in $e$. At any $x\ge q$ the same coefficient estimates give an additional factor $N^{-2(x-q)}$. The average regular contribution before the contour normalization is consequently at most $[3+(2(2-s)+2.5)A]\sqrt{B(s,\Delta)}/\log N$.

For the near zeros, apply Cauchy in $U$ to their logarithm sum times $\sup_{s\le x\le2}|D_Y(x+iU)|$. The latter has squared mean at most
\[
 \frac{(1+2r/\Delta)B(s-r,\Delta+2r)}{\pi r\log N},
 \qquad r=1/32.
\]
Indeed the submean inequality on a disk of radius $r$ bounds each point by the integral of $|D_Y|^2/(\pi r^2)$ on the common rectangle $[s-r,2+r]\times[U-r,U+r]$. Integrating in $U$ contributes an overlap of at most $2r$, and integrating $N^{-2(x-s+r)}$ in $x$ costs $1/(2\log N)$. These estimates are uniform in the vertical line $\eta$ approaching $s$.

## Numerical allowance and replay

Average the contour identity uniformly over $[T,V]$. The height average on its left vertical edge is exactly the integral with $W(t)$ in the displayed criterion. Set $e_{\rm edge}$ equal to the combined bounds for the pole, right edge and two horizontal edges divided by $K$. The [192-bit calculation](signed_contour.py) gives $h<.082942$, $e_{\rm edge}<.003614$, and computes the two deductions at the **same** rectangle to give
\[
     \min_{\text{30 rectangles}}(1-10^{-28}-h-e_{\rm edge})>.9164648 .
\]
Thus a failed count forces a strictly larger signed integral than the proposed upper allowance $.91646K$. This argument estimates all other contour terms. It does not establish the signed vertical integral bound.

## Removing an explicit Euler polynomial

In the remaining integral one may replace the log derivative by its difference from any $P_M(z)=\sum_{2\le m\le T^3}c_m m^{-z}$ with real $|c_m|\le\log m$. This includes either sign of a truncated von Mangoldt sum and arbitrary real taper weights of modulus at most one. The change to the normalized signed integral, in units of $K$, is less than **.000001706** throughout the thirty rectangles. To use this version one may retain the same proposed allowance $.91646K$, since $.91646+.000001706<.9164648$.

Indeed the cosine transform of $W$ at $\xi=\log(nm)$ equals $[\cos(T\xi)-\cos(V\xi)]/(\Delta\xi^2)$. Because $\xi^2\ge4\log N\log m$, the logarithm in the coefficient bound cancels. Writing $v=1/\log Y$ gives $\sum_{n>N}|a(n)|n^{-s}\Phi(b\log(Y/n))\le Y^{1-s+v}\exp((1-s+v)^2/(2b^2))(1+1/v)(1+\log(210N))$ by the same Gaussian bound used for the pole. Multiply this by $[1+((T^3)^{1-s}-1)/(1-s)]/(4\pi\Delta\log N)$ for the absolute change to the integral before division by $K$. Absolute convergence justifies the integrations. Proving the bound for the residual log derivative is still necessary.

~~~sh
python -B round5/spectrum/signed_contour.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. Codex derived this signed contour criterion.
