# Grouping the signed rational projections

This refines the [finite rational projection](RATIONAL.md) with the same paired sharp polynomials, AFE remainder and early-height terms. It permits all coprime unit pairs \(1\le s<r\le J\) in different bins, with \(J=65536\) in the verifier.

For \(Q=210,\alpha=1,w=.04,Z=384\) the resulting normalized fourth-moment upper bounds for every \(u\ge U\) are **.001147673** at \(U=35\), **.000997554** at \(U=37\), and **.000850665** at \(U=40\). The interval \([U,U+1]\) uses adjacent slab lengths \(.125,.25,.625\). Beyond it the previously proved \(J=512\) estimate starting at \(U+1\) supplies the uniform tail. The older [centered estimate](../../round6/phase/CENTERED_PHASE.md) was .001260749, .001106399 and .000954756 at the same three lower endpoints.

## Stationary approximation resolved at both endpoints

Retain the previous notation \(a=2\pi Rnj/Q\), \(l=(2\pi/Q)\max(n^2/\lambda,\lambda j^2)\), \(d_1=|\log(l/a)|\), \(d_2=|\log(T/a)|\). For each pair the error in its principal stationary contribution is bounded by
\[
 100+\min(9\sqrt a,2/d_1)+\min(9\sqrt a,2/d_2).                       \tag{1}
\]
As usual a zero distance has reciprocal \(+\infty\). The crude bound \(9+9\sqrt a\) is in the previous proof. For the regular bound use its same change of variable on the shorter reference interval \(0.9\le x\le1.1\). There \(|g'|\le .5/.9^2,\ |(h^2)'|\le1/(3\cdot .9^2),\ |g''|\le2/(3\cdot .9^3),\ |(h^2)''|\le1/(3\cdot .9^3)\), by integrating the powers of the parameter in the displayed integral definitions. Both \(g,h^2\) belong to \([1/1.1,1/.9]\). Differentiating gives \(|h'|<.217,|h''|<.29,|A|<1.161,|A_x|<1.04,|A_{xx}|<2.9\). Hence \(|A_v|<1.21,|A_{vv}|<5.2\). The \(vB(v)\) remainder is less than \(2(1.21)+(5.2/2)(.2/\sqrt{.9})<3\). The two constant-amplitude Fresnel tails cost at most \(4\sqrt{1.1}/.1<42\). Each actual endpoint beyond this fixed central interval costs at most \(2/\log(1.1)<21\); each actual endpoint inside it costs at most \(2/d_i\) on its omitted segment. If the saddle is not inside the original interval, its integral is already bounded by \(2/\min(d_1,d_2)\). This gives \(100+2/d_1+2/d_2\). Taking the lesser with the crude bound proves (1).

For an endpoint, let \(F(v)\) be the sum of its absolute amplitudes \(\mathbf1_{(n,Q)=1}|c_Q(j)|/\sqrt{Qnj}\) with \(d_i\le v\), and let \(L=L_f(T)L_d(T)\). If \(F(v)\le A_i v+B_i\) for \(0<v\le1\), the contribution from \(d_i>\delta\) to the minimum in (1) is bounded by
\[
 2L+2A_i\log(1/\delta)+2B_i/\delta ,
\]
as follows by writing the reciprocal as the integral of \(v^{-2}\). For \(d_i\le\delta\) add \(9\sqrt a\) times its absolute amplitude, by the previous boundary-count calculation. The verifier fixes \(\delta=8e^{-U/2}<.01\). Both ordinary \(2L\) terms and (1) give \(104L\); the opposite orientation still costs \(2L/\log R\).

Explicit \(A_i,B_i\) are obtained as follows, using \(\rho,\mu,D_f,D_d,C\) from the parent calculation. For the lower endpoint, sum the two strips centered at \(b=R,1/R\). On each strip \(1/\sqrt{nj}\le\sqrt e/(\sqrt{\lambda b}\,j)\) and there are at most \(2\rho\lambda j b\sinh(1)v+D_f\) eligible \(n\). Set \(Y_b=Y(T)\min(1,e/b)\), \(H_d=\mu(1+\log Y(T))+D_d\). The two coefficients for this strip can be taken as
\[
 A=\frac{\sqrt e}{\sqrt Q}2\rho\sqrt{\lambda b}\sinh(1)(\mu Y_b+D_d),
 \quad B=\frac{\sqrt e}{\sqrt Q}\frac{D_f H_d}{\sqrt{\lambda b}}.
\]
For the upper endpoint use \(1/\sqrt{nj}\le\sqrt{e/C}\). The corresponding pair is
\[
 A=\sqrt{e/(QC)}\,2\rho C\sinh(1)H_d,\qquad
 B=\sqrt{e/(QC)}\,D_f(\mu Y(T)+D_d).
\]
In a height slab use the upper endpoint for \(\log Y(T)\) inside \(H_d\), and the maximum or minimum permitted \(\lambda\) at the indicated products or denominators. All bounds divided by \(T\) now decrease apart from terms already frozen at the upper endpoint. The small-\(\delta\) bounds keep the exact \(\lambda Y(T)^2=QT/(2\pi)\) as in the parent proof.

## Arithmetic endpoint remainders

In the signed principal term put \(P=Qs\). Expand \(c_Q(j)\) as the sum of its \(\varphi(Q)\) unit additive characters. At fixed such character and fixed \(n\), a nonconstant geometric sum in \(j\) costs at most \(P/[2\min(d,P-d)]\), where \(d\) is its nonzero frequency residue \(hs-rn\bmod P\). This uses \(|\sin(\pi d/P)|\ge2\min(d,P-d)/P\). For \(d=0\) the error after subtracting the real interval length is at most one. Because \((r,P)=1\), as \(n\) ranges over a complete period these residues permute all classes. Summing absolute errors first over \(n\le X(T)\), then over the characters, therefore costs at most
\[
 (X(T)/P+1)\varphi(Q)P(2+\log P)
\]
before multiplying by \(2\pi\sqrt R/(QT)\). The mean principal term and the discrepancy from \(s\)-multiples retain their preceding bounds.

For the off-diagonal in \(E[S\cos(t\log R)]\) average the distances \(|rn-sm|\) over a full period in \(n\bmod s\). At fixed nonzero residue \(d\), charge \(1/d+1/(s-d)\) to the first representatives on its two sides; their remaining reciprocal sum is at most \(2(1+\log Y')/s\). At residue zero charge \(2/s\) for the first representatives and the same upper remainder. Since \(r\) permutes these residues, the total reciprocal sum is at most
\[
 2X'(1+\log Y')/s+(X'/s+1)(2+2\log s+2/s).
\]
Substitute this for the corresponding distance sum in the previous two-index estimate.

The test \(V_0\cos(t\log R)\) also permits \(R>\sqrt{Qt_0/(2\pi)}\). Above \(t'=(2\pi/Q)R^2\) both frequency derivatives are at least \(.25\). Below \(t'\), every active short-product index is at most \(R\) by its defining cutoff. Hence the normalized absolute upper is
\[
 h_0+2(t'/T)\sqrt{R D_M},\qquad h_0=4\sqrt{M D_M^{\rm up}}/(.25T).
\]
The second term can use \(D_M^{\rm up}\), and \(M\) in its denominator when reconstructed from \(h_0\) can be rounded down. The calculation takes the lesser upper whenever the previous all-time derivative is positive.

## Hilbert bound and bin weights

The doubled distinct frequencies \(\pm\log(r/s)\), with the fractions in lowest terms and \(s<r\le J\), have mutual gaps at least \((J^2+1)^{-1}\). Use the same [two-endpoint Hilbert inequality](../../round7/qrh_strip/INCREMENT.md), now with the common lower gap. For \(P(t)=\sum p_{rs}\cos(t\log(r/s))\) it yields
\[
 EP^2\le g\sum p_{rs}^2,\qquad g=\tfrac12+4.2(J^2+1)/T .
\]
Let \(S_r,V_r>0\) denote the two normalized residual variance bounds after the short-product step. Put \(\lambda_0=\sqrt{V_r/S_r}\) and \(\kappa=((U+b)/U)^4/\lambda_0\), where \(b\) is the slab length. Expand \(2E[(S-m-P)(V-V_0)]\) using \(2ab\le\lambda_0 a^2+b^2/\lambda_0\). Together with its compensation, the possible saving from the pre-existing covariance upper is at least
\[
 \frac{\lambda_0}{(U+b)^4}\sum[2p_{rs}(l_{rs}-\kappa h'_{rs})-g p_{rs}^2] .
\]
The variance deduction can be normalized at the upper slab endpoint because each term \(2p\,l-gp^2\) selected below is nonnegative. All positive restitution terms use the lower endpoint.

On a box in \(r,s\) let \(a_0>0\) be a certified lower bound for \(\sqrt{rs}(l_{rs}-\kappa h'_{rs})\). Choose \(p_{rs}=a_0/(g\sqrt{rs})\), for a saving at least \(\lambda_0 a_0^2/[g(U+b)^4]\) times the reciprocal pair mass. All box calculations in the [verifier](grouped_rational.py) substitute interval inputs in the real-coordinate bounds just proved. If an enclosure fails the positivity or logarithm test the entire box is omitted; the same bin on the two axes is also omitted.

For disjoint integer bins \(A=[a,b]\), \(B=[c,d]\), let \(N_A,S_A\) be the number and sum of the units in \(A\), and \(N_{A,p}\) the number of these divisible by \(p\nmid Q\). The actual coprime pair mass has the lower bound
\[
 \frac{N_A^2}{S_A}\frac{N_B^2}{S_B}
 -\frac{\sum_{p\le J,\,p\nmid Q}N_{A,p}N_{B,p}}{ac}.
\]
This follows by Cauchy on unrestricted harmonic masses, followed by the union bound for common prime factors. An empty bin contributes zero. The unit count at the divided integer endpoints gives the two \(N_{\cdot,p}\) exactly. The sieve and the binned matrix product use integer arithmetic; any entry of the sum of prime outer products is at most \(J^2\sum_{n\ge2} n^{-2}<2J^2\), and the entire unit first-moment prefix is at most \(J(J+1)/2\). The checked supported \(J\) keeps all signed 64-bit operations inside their range.

~~~powershell
python -B round8/critical/grouped_rational.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. Codex derived the boundary-distribution, residue-average and grouped projection calculation.
