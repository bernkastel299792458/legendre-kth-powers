# A direct estimate of the \(Q\)-sieved high norm

Write \(v=2+e,\ d=v-1,\ e=2\delta/\log T,\ e_0=2\delta/U,\ Y=hT,\ X=e^W Y\), with \(\log T\ge U,\ W>0,\ 0<h<1,\ 0<e_0\le.1\). Use the notation \(S_Q,\zeta_Q,b_{v,Q},\eta,D\) of the [sieved Selberg proof](VARIANCE.md), and let \(Y_0=he^U>1\). The function \(\texttt{direct_high}(U,\delta,W,\log h,Q)\) returns \(B_Q\) such that for \(e\ge l_0\ge0\)
\[
 T S_Q(2+e)\le Y^{-e}\,\frac{\zeta(2+l_0)}{\zeta(2)}\,B_Q .
\]
This replaces the complete high norm. The separate estimate of the \(1+e\) norm, including its variance deduction, is compatible.

For \(a(n)=\mu(n)\mathbf1_{(n,Q)=1}\), put
\[
 D_v=1/\zeta_Q(v),\qquad F_v=\sum_{n\ge1} a(n)n^{-v}\log n,\qquad
 R_v(t)=\sum_{n>e^t}a(n)n^{-v}(\log n-t).
\]
All series converge absolutely. For \(r=\log(j/Y)\), the defining taper or the identity \(\sum_{n\le e^t}a(n)n^{-v}(t-\log n)=tD_v-F_v+R_v(t)\) gives
\[
 W b_{v,Q}(j)=
 \begin{cases}
 R_v(-r)-R_v(W-r),&r\le0,\\
 rD_v+F_v-R_v(W-r),&0\le r\le W,\\
 W D_v,&r\ge W.
 \end{cases}
\]
These formulas agree at both endpoints.

Split \(0\le e\le e_0\) into eight closed cells \([l,u]\). Since \(\zeta_Q\) is a Dirichlet series with nonnegative coefficients, \(1/\zeta_Q(2+l)\le D_v\le1/\zeta_Q(2+u)\). Fix \(N=768\). Compute the finite Möbius sums for \(F_v\) and \(R_v\) with sign-respecting intervals. For \(t\in[a,b]\subset[0,\infty)\), the term in \(R_v\) before its weight lies in \([(\log n-b)_+,(\log n-a)_+]\). The tail of either finite sum is bounded in absolute value by \(\int_N^\infty x^{-2}\log x\,dx=(1+\log N)/N\). Here \(\log x/x^2\) decreases past \(N\).

Independently, the nonnegative function \(x^{-v}(\log x-t)_+\) is unimodal. Its sum is at most its integral plus its maximum, so
\[
 |R_v(t)|\le e^{-dt}/d^2+\frac{e^{-vt}}{\exp(1)\,v}\le1.2e^{-dt}.
\]
For each cell intersect this bound with the finite interval. When \(a\ge\log N\) the unimodal bound alone suffices.

To estimate \(A=Y^d\sum_{(j,Q)=1}j^{-v}|Wb_{v,Q}(j)|^2\), choose \(S=6\). For \(j\le Ye^{-S}\), the first line of the taper identity bounds \(|Wb_{v,Q}(j)|\) by \(1.2(1+e^{-W})(j/Y)^d\). The remaining power of \(j\) in \(A\) is \(j^{d-1}=j^e\). Use its maximum and the count of at most \(\eta Ye^{-S}+D\) admissible integers. This portion of \(A\) is at most
\[
 1.2^2(1+e^{-W})^2(\eta+D e^S/Y_0)e^{-(1+l)S}.
\]
Cover \([-S,0]\) by 96 equal cells and \([0,W]\) by 192 equal cells. On a cell \(a\le r\le b\), the number of admissible \(j\) on the corresponding half-open interval is at most \(\eta Y(e^b-e^a)+D\). The normalized weight on this cell is bounded by
\[
 \big(\eta(e^b-e^a)+D/Y_0\big)\exp(-(2+e')a),\qquad
 e'=\begin{cases}u,&a<0,\\l,&a\ge0.\end{cases}
\]
Multiply by the squared maximum absolute value of the interval for the appropriate taper identity. For \(j>X\), partial summation using \(\#\{X<j\le t:(j,Q)=1\}\le\eta(t-X)+D\) bounds the final part by
\[
 (\eta/(1+l)+D/Y_0)\,e^{-(1+l)W}\{W/\zeta_Q(2+u)\}^2.
\]
Any shared endpoint uses an adjacent cell that contains its true integrand. The count discrepancy \(D=2^{\omega(Q)}\) covers arbitrary nonintegral endpoints.

Let \(A_*\) be the maximum over all eight cells of the sum just obtained. The restricted Jordan-totient Cauchy bound gives \(S_Q(v)\le\zeta_Q(v)\sum_{(j,Q)=1}j^{-v}|b_{v,Q}(j)|^2\). Now \(\zeta_Q(v)\le\zeta(2+l_0)\prod_{p\mid Q}(1-p^{-2-e_0})\) whenever \(e\ge l_0\). Therefore
\[
 B_Q=\frac{\zeta(2)}{hW^2}\prod_{p\mid Q}(1-p^{-2-e_0})\,A_*
\]
has the claimed property. Running \(\texttt{python -B direct_high.py}\) for \(U=49,\delta=.9,W=10.7,\log h=-4.85\) returns \(B_2<.803707,\ B_6<.661518,\ B_{30}<.579229,\ B_{210}<.522956\).
