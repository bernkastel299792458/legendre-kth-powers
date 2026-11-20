# Fast short-mollifier arithmetic and the averaged diagonal

This supplements [SHORT.md](SHORT.md) and describes the optional engine [fast_short.py](fast_short.py) used by [short_block.py](short_block.py) when \(N\ge32768\). The attribution is the same. The integer double-sum method remains available for small supports.

## Real arithmetic identities

Write \(x_d=\lambda_d/d\), \(S_g=\sum_{g\mid d}x_d\), and \(J_s(g)=g^s\prod_{p\mid g}(1-p^{-s})\). Differentiating \(a^s=\sum_{g\mid a}J_s(g)\) gives the weighted gcd identity. Since \(J_1=\varphi\), put \(\ell_g=J'_1(g)/\varphi(g)=\log g+\sum_{p\mid g}\log p/(p-1)\). Then
\[
 A=\sum_g\varphi(g)S_g^2,\quad
 B=\sum_g\varphi(g)\sum_{g\mid d,e}x_dx_e(\ell_g-\log\max(d,e)).
\]
Process the distinct \(d\)'s in increasing order. For \(g\mid d\), let
\(z_{dg}=\varphi(g)x_d(2S_{g,\mathrm{prev}}+x_d)\).
Adding \(z_{dg}\) to \(A\) and \((\ell_g-\log d)z_{dg}\) to \(B\) gives both forms in \(O(\sum_{d\in{\cal D}}\tau(d))\) arithmetic operations after sorting. The index for \(g=bv\) is the pair consisting of the ranks of \(b\mid q\) and \(v\) in the squarefree coprime core. All such divisors are present. The memory for prefix sums is \(O(K)\), plus the short lists of divisors of the core indices.

## Binary64 certificate

The summation uses IEEE-754 binary64 round-to-nearest scalar arithmetic of the Numba nopython default with fast-math disabled. Write \(\epsilon=2^{-52}\), \(H=1+\log L\), \(\delta=(K+100)\epsilon<10^{-3}\). The looser unit \(\epsilon\) covers ordinary correctly rounded operations and square roots. The program limits \(qN<2^{32}, N\le2^{24}, s\le16,\ K\le32N\). All integer products and the exact sum \(\sum d\le KqN<2^{61}\) fit in signed 64 bits. Converting any individual integer operand in the floating path is exact. The smallest nonzero prefix on the \(x_d\)'s is a multiple of \(2^{-90}\), since all individual rounded summands have magnitude at least \(1/(16L)>2^{-36}\). The finite operations here stay far from underflow or overflow. The same conclusion holds for the Horner polynomial below; its intermediate coefficients are at least \(1/39\).

The integer logarithm routine uses \(h=\lfloor\log_2 n\rfloor,\ y=(n-2^h)/(n+2^h)\) with \(0\le y\le1/3\). It computes \(h\log2+2y\sum_{k=0}^{19}y^{2k}/(2k+1)\). The omitted series is less than \(2(1/3)^{41}/(41(1-1/9))<2^{-65}\). For \(n=1\) both values vanish. For \(n\ge2\), after distributing the positive Horner operations, each monomial uses fewer than 130 rounding factors including repeated appearances of the rounded \(y\) and \(y^2\). The relative error from the literal for \(\log2\) is below \(2\epsilon\), checked by Arb. Thus the computed logarithm has relative error below \(150\epsilon\). Each required \(\ell_g\) is a sum of at most 32 positive prime terms \(p\log p/(p-1)\); computing the two coprime parts and adding them gives relative error below \(220\epsilon\). In particular the absolute error in the final subtraction \(\ell_g-\log d\) is at most \(600\epsilon(1+3H)\); its exact absolute value is below \(3H\).

To control cancellation, write \(P_g=\sum_{g\mid d}|x_d|\) and \(w_{dg}=\varphi(g)|x_d|(2P_{g,\mathrm{prev}}+|x_d|)\). Then
\[
 \sum_{d,g\mid d}w_{dg}=\sum_g\varphi(g)P_g^2
 \le\sum_{d,e\le L}1/[d,e]\le H^3 .
\]
The last bound follows from the harmonic gcd sum in [SHORT.md](SHORT.md). For \(j\) consecutive roundings use \(\gamma_j=j\epsilon/(1-j\epsilon)\). A rounded running prefix differs from its exact value by at most \(\gamma_{K+1}P_{g,\mathrm{prev}}\le2(K+1)\epsilon P_{g,\mathrm{prev}}\), including the rounding of \(x_d\). Propagating this through the multiplication by \(\varphi(g)x_d\) and the addition \(2S+x_d\) bounds the individual absolute error in \(z_{dg}\) by \(10\delta w_{dg}\). Multiplication by two is exact. For example the prefix error contributes at most \(4(K+1)\epsilon\varphi(g)|x_d|P_{g,\mathrm{prev}}(1+\epsilon)^3\); the errors in the current summand and the remaining three arithmetic operations together are at most \(6\epsilon(1+2\delta)w_{dg}\).

For the \(B\) term, including the multiplication by the logarithmic difference gives an absolute error below \(20\delta(1+3H)w_{dg}\), using \(600\epsilon\le6\delta\). Within one \(d\) there are at most \(K\) summands and there are \(K\) outer sums. On each level the summation error is bounded by \(\gamma_K\) times the absolute sum on that level. Hence the script's enclosures with
\[
 E_A=64\delta H^3,\qquad E_B=64\delta H^3(1+3H)
\]
contain the true forms. It passes the upper endpoints of both forms and also \(E_A\), which recovers a lower bound for the negatively weighted occurrence of \(A\). The positive sums \(H_1,H_2,G,G_{\max},R\) each have relative error at most \(4(K+3)\epsilon\) including division, weight products and square root. The script encloses both \(H_1,H_2\) on both sides before the signed deduction. Bounds for \(G,G_{\max},R\) need only their upper endpoints. The final arithmetic and comparisons use Arb.

## Two analytic reductions at large support

For \(m=\lfloor z\rfloor\) define
\[
 F(z)=H_m-m(m+1)/(2z^2),\qquad
 J(z)=z^2(F(z)-\log z-\gamma+1/2).
\]
At integer \(m\ge1\), the standard harmonic bounds \(0<\log m+\gamma+1/(2m)-H_m<1/(12m^2)\) give \(-1/12\le J(m)\le0\). These follow by the alternating Euler–Maclaurin remainder for \(1/x\) (or the integral remainder from the trapezoid expansion for \(1/x\)). On \([m,m+1]\), \(J'(z)=2z(H_m-\log z-\gamma)\) in the interior. Its factor in parentheses is decreasing, so the minimum is attained at an endpoint. Also \(H_m-\log(m+1)-\gamma\ge-1/(m+1)\), hence \(J''(z)\ge-3\). The difference between \(J\) and its chord is therefore bounded above by \(3(z-m)(m+1-z)/2\le3/8\). For \(0<z<1\) use \(z^2|\log z|\le1/(2e)\) directly. Consequently \(|J(z)|\le3/8\) on the entire positive axis.

In fact \(|J(z)|\le1/6\). The quantity
\(a_m=\frac12\log(m^2+m+1/3)-H_m\) decreases to \(-\gamma\) for \(m\ge0\). With \(x=1/(m+1)\) its decrement satisfies
\(a_{m+1}-a_m=\operatorname{arctanh}(x/(1+x^2/3))-x\le0\), since the derivative of the negative of this last expression is \(x^4/(9-3x^2+x^4)\ge0\). Thus \(e^{2(H_m-\gamma)}\le m^2+m+1/3\). Each branch of \(J\) has its global maximum at \(z=e^{H_m-\gamma}\), where its value is \((e^{2(H_m-\gamma)}-m(m+1))/2\le1/6\). This reasoning includes \(m=0\); the lower bound on this first branch follows by taking its endpoint \(J(0)=0\) by continuity and the bound at 1. Together with the lower bounds on the other endpoints it proves the claim.

The diagonal integrand is a sum of squares at each \(t\), so \([200,Z]\) may be extended to \([0,Z]\) for it. The exact integral divided by \(Z\) of an individual harmonic term is \(F(Y(d,e)/\max(d,e))\). Thus replace \(B+(\gamma-\tfrac12\log(2\pi))A\) by \(B+(\gamma-\tfrac12\log(2\pi)-\tfrac12)A\). A valid intermediate estimate for the old integrated remainder \(2G/Y\) was
\[
 \frac{3}{8Y^2}\sum_{d,e}\frac{\max(d,e)}{\min(d,e)(d,e)}
 \le\frac{3H}{4Y^2}\sum_d d .
\]
The script uses the improved \(1/6\) in place of \(3/8\) and also keeps the small Euler divisors. For \(d=bn,e=cm\) with \(b,c\mid q\) one has \((b,c)\le(d,e)\). Taking the two orders, dropping their ordering restrictions after replacing the maximum and minimum, and retaining the absolute short weight \(w_m\) gives the remainder cap
\[
 \frac{1}{3Y^2}\sum_n n\sum_m\frac{w_m}{m}\sum_{b,c\mid q}\frac{b}{c(b,c)}
 =\frac{H_1}{3Y^2}\sum_d d\prod_{p\mid q}\left(1+\frac{2}{p(p+1)}\right).
\]
The \(m,n\) sums use the squarefree core. The equality follows by multiplying the four possibilities at each prime, whose sum is \(1+p+2/p\), and using \(\sum_d d=\sum_n n\prod_{p\mid q}(1+p)\). The script takes the minimum of the nonaveraged and improved averaged formulas. In the off-diagonal estimate it uses the exact \(G_{\max}=\sum_{d,e}1/\max(d,e)=\sum_{i=0}^{K-1}(2i+1)/d_i\), with \(d_i\) increasing, in place of \(2K\).

For any \(V>0\), direct integration gives \(\int_0^V|P|^2\le (V+4LH)H\). Indeed an off-diagonal ordered pair contributes at most \(2|\lambda_d\lambda_e|/(\sqrt{de}|\log(d/e)|)\), one has \(1/|\log(d/e)|\le L/|d-e|\), and every row of \(1/|d-e|\) has sum at most \(2H\). Apply \(2|a_da_e|\le |a_d|^2+|a_e|^2\) and \(\sum|\lambda_d|^2/d\le H\). Partial summation using this estimate gives
\[
 4\int_{200}^Z t^{-1/2}|P|^2dt \le (8\sqrt Z+16LH/\sqrt{200})H .
\]
Keep the old bound as another choice. On \([0,200]\) one has \(|\zeta(1/2+it)|\le6\sqrt{t+1}\). For \(t\le1\) this follows from the elementary integral in SHORT.md. For \(t\ge1\) use Euler summation at \(k=\lceil t\rceil\): the three terms are bounded by \(2\sqrt{k},\sqrt{k}\) and \(2(t+1)/\sqrt{k}\). Their sum is at most \((3+2\sqrt{2})\sqrt{t+1}\). The compact squared norm is thus at most \(36(200+200^2/2)R^2\). All these estimates are uniform for \(Z\ge e^U\) after division by \(Z\log Z\).

At \(U=39.98,\ q=210,\ W=9.5,\ \log h=-3.5\), run **python -B short_block.py --q 210 --n 2097152 --u 39.98 --split --local**. The old localized coefficient \(K_1<0.152628\) is replaced by \(K_1<0.137275\). The examples \(N=2^{15},2^{16},2^{17},2^{22}\) give \(K_1<0.142020,0.141176,0.140325,0.137015\), respectively.
