# Variance deducted from both centered Selberg bounds

For squarefree \(Q\), let \(\mathcal K\) be the semigroup of positive integers whose prime factors divide \(Q\), and put \(\zeta_Q(v)=\sum_{(n,Q)=1}n^{-v}\), \(Z=\zeta(v)/\zeta_Q(v)\). Write \(b_v(j)=\sum_m\mu(m)m^{-v}(1-\omega(jm))\) for the original centered coefficient. In the \(Q\)-sieved coefficient \(b_{v,Q}(j)\), restrict \(m\) to \((m,Q)=1\). The convolution of the unrestricted Möbius sequence with the indicator of \(\mathcal K\) shows that \(b_{v,Q}(j)=\sum_{k\in\mathcal K} k^{-v}b_v(jk)\). The centered Selberg inequality over \((n,Q)=1\) gives \(S_Q(v)\le\zeta_Q(v)\sum_{(j,Q)=1}j^{-v}b_{v,Q}(j)^2\). This follows from the same Jordan-totient expansion as the [original proof](../../round2/right/PROOF.md) with all divisors coprime to \(Q\).

The identity
\[
 Z\sum_{k\in\mathcal K} k^{-v}b_v(jk)^2
 -\left(\sum_{k\in\mathcal K} k^{-v}b_v(jk)\right)^2
 =\sum_{k<l,\ k,l\in\mathcal K}(kl)^{-v}(b_v(jk)-b_v(jl))^2
\]
holds by expansion and absolute convergence. Every integer has a unique decomposition \(jk\) with \((j,Q)=1,\ k\in\mathcal K\). Thus a lower bound on
\[
 \mathcal V_Q(v)=\zeta_Q(v)\sum_{\substack{j\ge1\\(j,Q)=1}}
      j^{-v}\sum_{\substack{k,l\in\mathcal K\\k<l}}
      (kl)^{-v}(b_v(jl)-b_v(jk))^2
\]
may be subtracted from the original upper estimate \(\zeta(v)\sum_{j\ge1}j^{-v}b_v(j)^2\). All omitted summands of the variance are nonnegative.

Write \(V=\log T\ge U,\ e=2\delta/V,\ e_0=2\delta/U,\ Y=hT,\ X=e^WY,\ Y_0=he^U,\ X_0=e^WY_0,\ \eta=\phi(Q)/Q\) and \(D=2^{\omega(Q)}\). Any interval of length \(x\), with one endpoint included, contains at least \(\eta x-D\) integers coprime to \(Q\), by inclusion–exclusion and the floor error \(<1\) for each divisor.

## The norm at \(v=2+e\)

For \(j\ge Y,\ r=\log(j/Y)\in[0,W]\), the [centered high-norm expansion](../../round2/right/fine/PROOF.md) gives \(W b_v(j)=rD_v+F_v-R_v(W-r)\), where \(D_v=1/\zeta(v)\ge6/\pi^2\) and \(|R_v(t)|\le1.2e^{-t}\) for \(t\ge0\). For \(k,l\in\mathcal K,\ k<l\), set \(r=\log(jk/Y),\ \lambda=l/k\). If \(0\le a\le r\le b\) and \(b+\log\lambda\le W\), then
\[
 W(b_v(jl)-b_v(jk))\ge \tfrac6{\pi^2}\log\lambda-1.2(1+\lambda)e^{b-W}.
\]
Take the positive part and square it. For a half-open cell \(a<r\le b\), the weight of \(j\) is at least its count times \(((Y/k)e^b)^{-v}\). After multiplication by \(T(kl)^{-v}\), this is at least
\[
 \frac{Y^{-e}}{h\,k\,l^{2+e_0}}\,
 \big[\eta(e^b-e^a)-Dk/Y_0\big]_+e^{-(2+e_0)b}.
\]
The code sums these products over \(r\in[0,4]\) in cells of width \(1/16\) and smooth \(k<l\le96\). It retains only cells entirely in the transition range. The prefactor \(\zeta_Q(2+e)\ge\zeta_Q(2+e_0)\) is evaluated through its finite Euler product with \(\zeta(2+e_0)\). This proves
\[
 T\mathcal V_Q(2+e)\ge Y^{-e}\,\texttt{high_saving}(U,\delta,W,\log h,Q).
\]

## The norm at \(v=1+e\)

Put \(r=\log(X/(jk))\). When \(0\le r\le\min(W,\log(l/k))\), the first argument \(jk\) is in the transition and the second \(jl\ge X\). The endpoint values in the [centered low-norm formula](../../round2/right/fine/PROOF.md) give \(W(b_v(jl)-b_v(jk))=G_e(r)\). In equation (2) of that proof the terms beyond \(e^{-er}G_0(r)\) are nonnegative. For \(r\le\log2\) one has \(G_0(r)=r\), including both endpoints. For \(\log2\le r\le\log512\), \(G_0(r)>.65\) follows by direct evaluation at \(\log n,\ 2\le n\le512\), because \(G_0\) is linear between consecutive breakpoints. The program recomputes and checks all these values using exact integer Möbius coefficients and Arb. On a grid cell \(a\le r<b\) this gives \(G_e(r)\ge e^{-e_0 b}\min(a,.65)\).

The count of eligible \(j\)'s times their smallest possible \(j^{-v}\), multiplied by \((kl)^{-v}\), is at least
\[
 \frac{X^{-e}}{k l^{1+e_0}}\,[\eta(e^{-a}-e^{-b})-Dk/X_0]_+\,e^a.
\]
Finally \(\zeta_Q(1+e)/V\ge \eta/(2\delta)\) and \(X^{-e}\ge Y^{-e}e^{-e_0W}\). The code sums eligible cells for smooth \(k<l\le512\). This proves
\[
 \mathcal V_Q(1+e)/V\ge Y^{-e}\,\texttt{low_saving}(U,\delta,W,\log h,Q).
\]

Both deductions are made within a bound with the *actual common factor* \(Y^{-e}\), before replacing it by its cell upper bound. If the numerical high-norm implementation multiplies its uniform base by \(\zeta(2+l_0)/\zeta(2)\le1\), where \(l_0\) is the cell's lower endpoint for \(e\), it is also valid to subtract \(\texttt{high_saving}\) from that base before this extra multiplier. The actual low coefficient can be reduced by \(\texttt{low_saving}\) before the same \(Y^{-e}\) replacement. The old coefficient expressions from [the pole bound](../../round2/spectrum/pole_norm.py) have the required common factor.

Running \(\texttt{python -B variance.py}\) uses \(U=49,\delta=.9,W=10.7,\log h=-4.85\). For \(Q=6\) it gives high and low deductions exceeding \(0.11906322\) and \(0.0005031006\), respectively.
