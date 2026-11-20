# A joint second moment for the short mollifier

The [fast divisor sums and averaged diagonal](FAST_SHORT.md) give the large-support implementation and sharpen the two remainder terms below.

Claude and Codex research workspace. Codex derived the estimates below. The result is an auxiliary unconditional critical-line bound for the conditional fourth-power route. The proof uses the explicit Riemann–Siegel inequality cited in the [earlier boundary proof](../../round3/critical/PROOF.md). The finite arithmetic uses Arb and 64-bit integer gcd sums. No Lean verification is claimed.

Let \(q\) be the selected squarefree modulus with \(6\mid q\). For a fixed integer \(N\), put
\[
P(s)=E_q(s)\sum_{n\le N,(n,q)=1}\mu(n)n^{-s}
=\sum_{d\in{\cal D}}\lambda_d d^{-s},\qquad E_q(s)=\prod_{p\mid q}(1-p^{-s}).
\]
Here \(\lambda_d=\pm1\), \(K=|\mathcal D|,\ L=\max \mathcal D,\ R=\sum d^{-1/2}\). The disjoint representation of each coefficient is \(d=bn,\ b\mid q,\ (n,q)=1\). In this document \(Z\) denotes time height, \(u=\log T\) is the density boundary parameter.

## A mixed second moment

For \(Z\ge e^U,\ U>20\), write \(Y=(Z/(2\pi))^{1/2}\). On \(200\le t\le Z\) the ordinary Riemann–Siegel formula bounds \(|\zeta(1/2+it)P(1/2+it)|\) by \(2|D_yP|+2t^{-1/4}|P|\), where \(D_y=\sum_{n\le y} n^{-1/2-it}\) and \(y=\sqrt{t/(2\pi)}\). The direct and reflected polynomials have identical pointwise modulus at this line. The initial interval satisfies \(|\zeta|\le403\), using \(\zeta(s)=s/(s-1)-s\int_1^\infty\{x\}x^{-s-1}dx\). Thus the initial interval and the high-height Riemann–Siegel remainder have combined squared norm at most \(R^2(200\cdot403^2+8\sqrt Z)\).

The diagonal of \(|D_yP|^2\) equals
\[
 \sum_{d,e}\frac{\lambda_d\lambda_e}{[d,e]}
 H_{\lfloor y(d,e)/\max(d,e)\rfloor}
 = A(\log y+\gamma)+B+O(G/y),
\]
where \(A=\sum\lambda_d\lambda_e/[d,e]\), \(B=-\sum\lambda_d\lambda_e\log(\max(d,e)/(d,e))/[d,e]\), \(G=\sum1/\min(d,e)\). The constant in the error is one. For \(x\ge1\), \(|H_{\lfloor x\rfloor}-\log x-\gamma|\le1/x\) follows from the two endpoint harmonic inequalities and monotonicity of \(\log x\pm1/x\) on this range. For \(0<x<1\) it follows from \(x|\log x+\gamma|\le x\gamma+x|\log x|\le\gamma+1/e<1\). Positivity \(A\ge0\) follows by the gcd expansion with \(\varphi\). Integrating costs at most \(2GZ/Y\) for the error. With bounds \(a_-\le A\le a_+\) and \(B\le b_+\), the diagonal divided by \(Z\log Z\) is at most
\[
 a_+/2+[(\gamma-\tfrac12\log(2\pi))a_-+b_+]_+/U+2G/(Y_0 U),
 \qquad Y_0=\sqrt{e^U/(2\pi)}.
\]
One may integrate the nonnegative constant majorant at the upper height across \([0,Z]\).

For an off-diagonal pair of frequencies \(a=dm>b=en\), the moving lower cutoff supplies just one integration interval and hence costs \(2/\log(a/b)\). From \(\log(a/b)\ge (a-b)/a\) and \(\sqrt{a/b}\le 1+(a-b)/\sqrt{ab}\),
\[
 \frac1{\sqrt{ab}\log(a/b)}\le\frac1{a-b}+\frac1{\sqrt{ab}} .
\]
The shift \(h=dm-en>0\) is a multiple of \(g=(d,e)\). For fixed \(h\), the variables \(m,n\le Y\) advance in steps \(e/g,d/g\), so there are at most \(1+Yg/\max(d,e)\) choices. Also \(\sum_{d,e}1/\max(d,e)\le2K\) by ordering the distinct indices. Summing the positive shifts through \(LY\), treating both orders and charging the trivial separated sum of \(1/\sqrt{ab}\), gives the bound
\[
 4(1+\log L+\tfrac12\log Z)(K^2+2KY)+16YR^2 .
\]
Each term after division by \(Z\log Z\) is uniformly bounded at \(Z=e^U\). Minkowski's inequality on the main and error terms yields the coefficient \(S(U)\) computed by **short_second**, with \(\int_0^Z|\zeta P|^2dt\le S(U) Z\log Z\).

## A first moment and the affine density estimate

Shifting the segment \(\Re s=1/2,\ |\Im s|\le Z\) to \(\Re s=2\) proves
\[
 \left|\int_0^Z\Re(\zeta P)(1/2+it)\,dt-Z\right|\le20(1+R)\sqrt Z .
\]
The two halves are conjugates. The absolute contribution off the constant on the right edge, after halving, is at most \(\zeta(2)^2/\log2\). The pole costs at most \(\pi R\). On either horizontal edge \(|P|\le R\) and \(|\zeta(s)|\le5\sqrt Z\) for \(Z\ge200\), by truncating Euler summation at \(\lfloor Z\rfloor\): the three terms are bounded by \(2\sqrt Z,\sqrt Z/Z,2(Z+2)/\sqrt{\lfloor Z\rfloor}\). Horizontal length is \(3/2\). These bounds imply the displayed coefficient with room.

Use the weight \(g(t)=\min(1,(vT/t)^m)\), \(v=1.01,\ m=2048\). Its layer-cake is a mixture of \([0,Z]\) with \(\mathbb E Z=\bar y T,\ \bar y=vm/(m-1)\). Since \(\log(Z/T)\le u[(Z/T)^{1/u}-1]\), we get
\[
 \mathbb E[Z\log Z]\le Tu\,v^{1+1/U}m/(m-1-1/U)=Tu\,J(U),\qquad u\ge U.
\]
Also \(\mathbb E\sqrt Z\le\sqrt{\bar y T}\). For \(0<\eta\le1\), apply both moments to \(\eta\zeta P-1\). The resulting \(L^{4/3}(g\,dt)\) norm divided by \(T^{3/4}u^{3/2}\) is bounded by
\[
 {\bar y^{1/4}\over U}
 \left(\eta^2 S(U)J(U)+[1-2\eta]_+\bar y/U+\min(1-2\eta,0)\bar y/V+
 40\eta(1+R)\sqrt{\bar y}\,e^{-U/2}/U\right)^{1/2}.
\]
This is Hölder from the second moment, including the first moment with its sign. Here the row satisfies \(U\le u\le V\), which permits its negative term to be frozen at the right endpoint.

The remaining polynomial for the filtered fourth moment is
\(E_{q/6}\sum_{(n,q)=1}\mu(n)(\omega(n)-\eta\mathbf1_{n\le N})n^{-s}\).
Require \(N<e^{U+\log h}\) and \((q/6)N < (6v\cdot1.03/\pi)e^U\).
Then all the changed coefficients have \(\omega=1\), and every changed physical frequency is in the affine small-frequency range. For a fixed \(T\) the unnormalized harmonic square on that range drops by *exactly*
\[
 (2\eta-\eta^2)\,r_q H_N,\qquad
 r_q=\prod_{p\mid q/6}(1+1/p),\quad H_N=\sum_{n\le N,(n,q)=1}\mu(n)^2/n.
\]
Every other energy majorant is monotone in the squares of coefficients and may be retained. For the [localized mean](../spectrum/critical_mean.py), its layer-cake restricted to \(Z\le1.03\,vT\) has average at least
\(D=\bar y(1-1.03^{1-m})\) in units of \(T\). The affine harmonic prefactor is at least one in addition to that average. The support check places every short frequency in the small range of every local logarithmic window to which it belongs. The enlarged overlapping frequency envelopes used in the previous proof also contain every changed coefficient in the harmonic head. For \(U\le u\le V\) one may therefore replace the previously certified uniform multiplier \(C_M(U)\) by
\[
 C_{\rm res}= C_M(U)-D(2\eta-\eta^2)r_qH_N/V .
\]
In particular, taking the positive part of the harmonic offset in the old upper bound does not weaken this deduction. One first applies the very same affine upper majorant to the residual coefficients, then uses the upper bound for its unsubtracted harmonic and the lower bound for the amount removed. For the former global folded mean with coefficient \(D_U\), fix its common affine majorant at \(U\) and subtract its own coefficient \(D_U\) instead.

Finally, add \(C_{4,g}(U)^{1/4}\sqrt{C_{\rm res}}\) to the short norm above, and take the \(4/3\) power. Each choice of \(\eta\) is valid on the entire row. **split_endpoint** takes the minimum of the old and new estimates in each of eight closed unit rows and the old estimate above the eighth row. The maximum of the nine outputs covers the full half-line. Its **cm_local** adapter applies to the round-five localized critical mean.

## Integer and interval evaluation

Each \(1/[d,e]\) is replaced by \(2^{-44}\lfloor 2^{44}/[d,e]\rfloor\). The signed numerator sums are grouped by \(j=\max(d,e)/(d,e)\), using the two orders for a strict pair. Errors for \(A,B\) are bounded by \(K^2/2^{44}, K^2\log L/2^{44}\), respectively. Every partial or final signed accumulator has absolute value at most
\[
 2^{44}\sum_{d,e\le L}\frac1{[d,e]}
 =2^{44}\sum_{j\le L}\frac{\varphi(j)}{j^2}H_{\lfloor L/j\rfloor}^2
 \le 2^{44}(1+\log L)^3<2^{62}.
\]
The script also checks \(L^2<2^{62}\) before forming integer products. The logarithms of \(j\), the finite harmonic, all remaining constants and all volume comparisons are evaluated with Arb. Run **python -B short_block.py --q 210 --n 4096 --u 43 --split --local** to reproduce the localized comparison.

An optional experiment replaces \(\mathbf1_{n\le N}\) by the average \(w_n\) of the first \(s\) indicators \(\mathbf1_{n\le N/2^i}\), \(0\le i<s\), selected by **--steps**. The change in harmonic mass then uses \(2\eta\sum\mu(n)^2w_n/n-\eta^2\sum\mu(n)^2 w_n^2/n\) on the same index set. Multiply each finite gcd coefficient by \(w_n w_{n'}\) before rounding; the error bounds are unchanged, and the additional integer products are checked against \(2^{62}\). All absolute-value remainder estimates still use \(|\lambda_d|\le1\). With \(q=210,N=4096,U=43\), the three-step average improves the mixed second moment coefficient from \(0.76173\) to \(0.68743\), but it removes less harmonic mass. The resulting \(K_1<0.13330\) is weaker than \(K_1<0.13305\) from the sharp cutoff.
