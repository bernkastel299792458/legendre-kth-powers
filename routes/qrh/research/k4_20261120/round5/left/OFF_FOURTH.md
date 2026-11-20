# The off-diagonal fourth moment with a common moving cutoff

Put \(Y=\sqrt{T/(2\pi)}\), \(Y_0=\sqrt{e^U/(2\pi)}>200\), and \(E_6(s)=(1-2^{-s})(1-3^{-s})\). For the four [filtered Riemann–Siegel rows](../../round4/density/SIEVED.md), a raw index \(a\le y=\sqrt{t/(2\pi)}\) contributes the physical index \(ia\). The types \(i=1,2,3,6\) require respectively \((a,6)=1\), unrestricted, odd, unrestricted. Write \(\delta_i\) for their densities and \(e_i\) for their interval discrepancies. The tails require \(y<\lambda_i a\), with \((\lambda_1,\lambda_2,\lambda_3,\lambda_6)=(\infty,2,3,2)\). Each fixed row quadruple is active on one time interval.

For rows \(i,j,k,l\), write \(m=Aab>n=Bcd\), \(A=ij,B=kl\), and \(a,b,c,d\le Y\). The two roles in either product can be interchanged. Integration costs \(2/\log(m/n)\). For \(x=\log(m/n)>0\),
\[
  \frac1{\sqrt{mn}\log(m/n)}
   \le\frac1{m-n}+\frac{.118}{\sqrt{mn}} .
\]
The difference times \(\sqrt{mn}\) is \(1/x-1/(2\sinh(x/2))\). For \(x\le1\), compare the series termwise to obtain \(\sinh(x/2)/(x/2)\le(1-x^2/24)^{-1}\). For \(x\ge9\) the difference is at most \(1/x\). For \(1\le x\le9\) the script bounds the two monotone terms at opposite endpoints of closed cells of width \(1/1024\). The count in a row up to \(z\ge1\) is at most \(\delta_i z+1\), so its raw \(1/\sqrt a\) sum is at most \(2\delta_i\sqrt Y+1\) by partial summation. The two orientations together cost at most \(32(.118)Y^2(\sum_i (\delta_i+1/(2\sqrt{Y_0}))/\sqrt i)^4\) for the additive remainder.

## Two sums over fixed indices

Set \(G=(Aa,Bc)\), \(M=\max(Aa,Bc)\), \(m_0=\max(a,c)\). Every contributing pair lies in the convex polygon \(D=\{(a,c):0<a,c\le Y,\ c\le\lambda_i a,\ a\le\lambda_k c\}\). The two inner variables are each at least \(m_0w\), where \(w=\min(1/\lambda_j,1/\lambda_l)\). Use the normalized bounds over admissible \(a,c\):
\[
 F\ge Y^{-2}\sum_D1/G,\qquad
 S\ge Y^{-2}\sum_D Y/M,\qquad
 S'\ge Y^{-2}\sum_D(Y-m_0w)/M .
\]

The relative area of \(D\) is \(v=1-1/(2\lambda_i)-1/(2\lambda_k)\). For \(g=(A,B),s=30\), let \(K\) be the average of the two residue indicators divided by \(g\,((A/g)a,(B/g)c,s)\) over all \(s^2\) residue pairs. This denominator divides \(G\). Then \(F=(v+4s/Y_0+4s^2/Y_0^2)K\) works. For each pair of residue classes surround the lattice points by disjoint half-open squares of side \(s\). Their union lies inside \(D+[-s,s]^2\). Expanding a convex set in each coordinate in turn shows that the increase in area is at most \(2s\) times the sum of its coordinate widths plus \(4s^2\).

The integral of \(1/\max(Ax,Bz)\) over \(D/Y\) is
\[
 J=\int_{1/\lambda_i}^{\lambda_k}
       \frac{\min(1,1/r)}{\max(Ar,B)}\,dr ,
\]
using \(x=rz\). The script integrates its four elementary pieces at the breakpoints \(1,B/A\). The polygon cut by \(M\le t\) has coordinate widths at most \(\min(Y,t/A),\min(Y,t/B)\). Its allowed lattice count is bounded by \(\delta_i\delta_k\) times its area plus the corresponding expansion error from squares of side 6 inside this factor. Integrate the counts against \(dt/t^2\) on \([1,\infty)\), enlarging only the area integral to \([0,\infty)\). The result is
\[
 S=\delta_i\delta_k\left[J+\frac{144+12((1+\log(AY_0))/A+(1+\log(BY_0))/B)}{Y_0}\right].
\]
All normalized errors decrease for \(Y\ge Y_0\). For \(S'\) subtract from \(S\) the quantity \((\delta_i/2-2/Y_0)(\delta_k/2-2/Y_0)w/\max(A,B)\). The rectangle \((Y/2,Y]^2\) belongs to \(D\), each of its two side counts is at least \(\delta_i Y/2-2\) for the respective row, and \(m_0/M\ge1/\max(A,B)\).

## Positive shifts

Choose \(c_*\in\{1/2,1,2\}\). For \(0<h=m-n\le c_*GY\), put \(h=Gv,\ P=Aa/G,\ Q=Bc/G\). The solutions of \(P b-Q d=v\) have steps \((Q,P)\), and their parameter interval has length at most \(H=(Y-m_0 w)G/M\). For each \(v\bmod6\) the allowed parameters are periodic modulo 6. Let \(r_v\) be their density and \(d_v\) their upper interval discrepancy. The script considers all \(P,Q\bmod6\) with \((P,Q,6)=1\), all \(v\bmod6\), and one solution to each congruence. The six shifts yield its six distinct solutions. For allowed positions \(t_0<\cdots<t_{k-1}\) modulo 6, the discrepancy bound is \(\max_j(j+1-r_vt_j)-\min_j(j-r_vt_j)\), valid also for closed endpoints. An empty set has discrepancy zero. The solution count is therefore at most \(d_v+r_vH\), and also at most \(1+H\).

For \(r=1,\ldots,6,\ Z\ge96\), the harmonic sum through \(Z\) in residue \(r\) is at most
\[
 \log Z/6+\kappa_r,\qquad
 \kappa_r=\sum_{a=0}^{15}(r+6a)^{-1}-\log(r+90)/6 .
\]
This follows by integrating after the sixteenth term. Over all step pairs let \(D_0,D_1,R_1\) respectively bound the period mean of \(d_v\), \(\sum_r d_r\kappa_r\), and \(\sum_r r_r\kappa_r\). The mean of \(r_v\) equals \(\delta_j\delta_l\), since all six congruences account for every allowed pair modulo 6 once. Writing \(z=\log(c_* Y)\), the normalized contribution is at most either
\[
 (D_0z+D_1)F+(\delta_j\delta_l z+R_1)S',
 \qquad (1+z)(F+S').
\]

For \(h\ge c_*GY\), fix the inner variable multiplying the smaller of \(Aa,Bc\). The remaining variable belongs to a row of density \(\delta_t\). The spacing in unrestricted values of \(h\) is \(M\). Integration by level sets bounds the sum of \(1/h\) by \(\delta_t\log(AY/c_*)/M+e_t/(c_*GY)\), since \(h\le AY^2,\ G\ge1\). The fixed variable has at most \(\delta_o(Y-m_0w)+e_o\) choices. Write \(b_0=\max(\delta_j e_l,\delta_l e_j)\). Multiplying and summing over \(a,c\) gives the normalized bound
\[
 F\frac{b_0+e_je_l/Y_0}{c_*}
 +\left(\delta_j\delta_l S'+\frac{b_0}{Y_0}S\right)\log(AY/c_*).
\]
A shift at the common endpoint may be counted twice. For each ordered quadruple the script selects one orientation inside each product, one \(c_*\), and one of the small-shift bounds. Every chosen affine polynomial applies for all \(T\ge e^U\); the choice is made at \(U\).

Sum over ordered row types, multiplying by \(4Y^2/T=4/(2\pi)\) for both orientations and the exponential integral, then add the .118 remainder. This gives the off-diagonal polynomial used together with the [diagonal proof](PROOF.md) and the Riemann–Siegel remainder. Running **python -B off_fourth.py** gives an off-diagonal bound \(474.259006T\) at \(\log T=40\), and the complete uniform bound
\[
 \int_0^T|\zeta(1/2+it)E_6(1/2+it)|^4\,dt
 < .009329334\,T\log^4 T\qquad (T\ge e^{40}).
\]
