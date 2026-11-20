# The fourth moment with the Euler factor at 2 removed

Put \(E(s)=1-2^{-s}\) and \(s=1/2+it\). The function \(\texttt{fourth_two}(U)\) returns a uniform coefficient \(C(U)\) in
\[
 \int_0^T |\zeta(s)E(s)|^4\,dt\le C(U)T\log^4 T,\qquad T\ge e^U,\quad U\ge20.
\]
For \(U=49\) it is less than \(0.018198893\). This is a written inequality for the sieved critical-line factor with Arb checks of its scalar bounds. It may be used with the separate second moment of a Dirichlet polynomial supported on odd indices.

For \(t\ge200\), Hiary's Riemann–Siegel estimate gives
\[
 |\zeta(s)E(s)|\le 2|F(t)|+2(1+2^{-1/2})t^{-1/4},\qquad
 F(t)=E(s)\sum_{n\le y}n^{-s},\quad y=\sqrt{t/(2\pi)}.
\]
This inequality uses \(|E||\Re(e^{i\vartheta}D)|\le|ED|\). On the lower segment \(0\le t\le 200\), use \(|\zeta E|\le403(1+2^{-1/2})\) as in the [unfiltered proof](../../round3/critical/PROOF.md). [Hiary, equation (11)](https://www.sciencedirect.com/science/article/am/pii/S0019357715000865).

The coefficient of \(n^{-s}\) in \(F\) is \(1\) for odd \(n\le y\) and \(-1\) for even \(y<n\le2y\). Write \(O\) and \(B\) for the two positive sets. The time range of each fixed index is one interval. The same holds for any four fixed indices.

## Diagonals at a fixed height

Let \(J_{UV}\) be the weighted energy of products \(ab=cd\) with \(a,c\in U\) and \(b,d\in V\), with weight \(1/(ab)\). Write \(z=\log y\) and \(h=1+z/2\). For any \(x\ge1\), \(\sum_{n\le x,\ n\ {\rm odd}}1/n\le 1+\frac12\log x\), by comparing each summand after \(n=1\) with the integral over \([n-2,n]\). The parametrization \(a=gr,\ c=gs,\ b=js,\ d=jr\), \((r,s)=1\), gives the following bounds.

* For \(O,O\) all four parameters \(g,j,r,s\) are odd. Drop the coprimality constraint. The cumulative harmonic pair mass through \(e^v\) is at most \((1+v/2)^2\). Bound the remaining squared harmonic sum by \((1+(z-v)/2)^2\) and apply partial summation. The resulting bound is
\[
 J_{OO}\le (1+z/2)^2+\int_0^z (1+v/2)^2(1+(z-v)/2)\,dv
 =1+2z+z^2+z^3/6+z^4/96.
\]
* For \(O,B\), \(r,s,g\) are odd and \(j\) is even. By symmetry take \(r\le s\le2r\) and multiply by 2. For \(j=2k\), the admissible \(k\)'s lie in an interval \((A,2A]\), whose harmonic mass is at most 1. Indeed if \(q=\lfloor A\rfloor\) it has at most \(q+1\) entries, each at least \(q+1\). Thus the harmonic mass of \(j\) is at most \(1/2\) and that of \(g\) is at most \(h\). The odd \(s\in[r,2r]\) have harmonic mass at most \(1/r+(\log 2)/2\), by the same step-two integral. Therefore
\[
 J_{OB}\le h\big(3\zeta(2)/4+(\log 2)h/2\big).
\]
* For \(B,B\), divide all indices by \(2\). The new four indices belong to \((y/2,y]\), giving a weight factor \(1/4\). Both \(g,j\) range over intervals of ratio at most two, so each harmonic sum is at most 1. The condition \(r\le s\le2r\) and symmetry cost at most \(2\sum_{r\le y}(1/r)(1/r+\log2)\). Consequently
\[
 J_{BB}\le \tfrac12\{\zeta(2)+(1+z)\log2\}.
\]

In \(F^2\) the \(O,O\) products are odd and the other products are even. The squared \(\ell^2\) norm of its product coefficients therefore satisfies
\[
 Q(z)\le J_{OO}+(2\sqrt{J_{OB}}+\sqrt{J_{BB}})^2
 \le J_{OO}+\frac{14}3 J_{OB}+7J_{BB}.
\]
Here the last line uses \(2ab\le a^2/6+6b^2\). The code uses the three polynomial upper bounds on the right.

## Nonzero product shifts and the uniform moment

At \(T\) all four indices lie below \(2Y\), with \(Y=\sqrt{T/(2\pi)}\). On a non-diagonal quadruple, integrating its exponential on its single activity interval costs at most \(2/|\log(ab/cd)|\). Dropping its sign, parity and activity restrictions now yields the off-diagonal bound of the [unfiltered shifted-product argument](../../round3/critical/PROOF.md) with \(Y\) replaced by \(2Y\). This is
\[
 4Y^2\{4(1+2\zeta(2))(1+2\log(2Y))+16\}.
\]
For the diagonal integrate the polynomial \(q(u)=Q((u-\log(2\pi))/2)\) at the actual height \(u=\log t\). If \(A=q-q'+q''-q'''+q''''\), the integral from \(200\) to \(T\) is \(T A(\log T)-200A(\log200)\). Divide by \(T\), majorize the second term by its positive part at \(e^U\), and add the off-diagonal polynomial divided by \(T\). For the resulting coefficients \(p_j\), \(V=\sum_{j=0}^4\max(0,p_j)U^{j-4}\) bounds \(\int_{200}^T|F|^4/(T\log^4T)\).

The two errors on disjoint time ranges have fourth-power integral at most \((1+2^{-1/2})^4(200\cdot403^4+16\log T)\). Minkowski and the decrease of \(u e^{-u}\) finish the proof. Use \(\texttt{python -B sieved_fourth.py}\) to reproduce the numbers.

## Removal of both Euler factors at 2 and 3

Let \(E_6(s)=(1-2^{-s})(1-3^{-s})\). The same construction gives \(\texttt{fourth_six}(49)<0.017001453\) and \(\texttt{fourth_six}(54)<0.013607895\). For \(E_6\sum_{n\le y}n^{-s}\) the moving terms admit these four representations \(n=ij\), each with a single time interval for fixed \(i,j\).

| \(i\) | condition on \(j\) | condition on \(ij\) | coefficient |
|---|---|---|---|
| \(1\) | \((j,6)=1\) | \(j\le y\) | \(+1\) |
| \(2\) | any | \(y<2j\le2y\) | \(-1\) |
| \(3\) | \(j\) odd | \(y<3j\le3y\) | \(-1\) |
| \(6\) | any | \(3y<6j\le6y\) | \(+1\) |

Indeed for each \(n\) the coefficient is \(\sum_{d\mid (n,6),\,d\ge n/y}\mu(d)\). The two active pieces of an \(n\) divisible by 6 never overlap at a fixed height. Each \(j\le y\).

Write \(A\) for the first row, \(B\) for the union of the three tails at a given time, \(h=1+(\log y)/3\), \(v=(\log y)/3\) and \(H_5=\sum_{n=1}^5 1/n\). All tail coefficients at that time have absolute value at most 1. Since \(A\) is coprime to 6 and each \(n\in B\) is divisible by 2 or 3, \(A^2\) has support disjoint from \(AB\) and \(B^2\). Thus the same energy reduction applies, using \(J_{AA}+(20/3)J_{AB}+(5/2)J_{BB}\).

For \(z\ge1\), \(\sum_{n\le z,(n,6)=1}1/n\le1+(\log z)/3\). For \(z<5\) this follows from the lone \(n=1\). For \(z\ge5\) integrate over step-six intervals before each term in the classes \(1,5\bmod6\) after their initial entries. This gives the constant \(1+1/5-(\log5)/6<1\). The corresponding partial summation for \(J_{AA}\) gives \(1+4v+4v^2+4v^3/3+v^4/6\).

For an interval \((t,6t]\), its harmonic mass is at most \(H_5\). Indeed for \(q=\lfloor t\rfloor\) it is at most \(H_{6q+5}-H_q\), which decreases with \(q\), since the six terms newly added are at most \(1/(q+1)\) in sum. Its portion divisible by 2 or 3 has mass at most \(5H_5/6\) by the union bound after scaling by those primes. For \(r\ge1\), the coprime-to-6 mass of \([r,6r]\) is at most \(2/r+(\log6)/3\), paying for the first term and then integrating over step six in each residue class. In the energy \(J_{AB}\), \(g,r,s\) are coprime to 6 and \(j\) is divisible by 2 or 3. With \(r\le s\le6r\), apply these last two bounds to \(s,j\). Using \(\sum_{(r,6)=1}1/r^2=2\zeta(2)/3\) gives
\[
 J_{AB}\le 2(5H_5/6)h\big(4\zeta(2)/3+h(\log6)/3\big).
\]
For \(J_{BB}\), drop the residues and use that all indices belong to \((y,6y]\). The two harmonic sums over \(g,j\) are at most \(H_5\) apiece. With \(r\le s\le6r\), \(r\le6y\), one obtains
\[
 J_{BB}\le 2H_5^2\{\zeta(2)+(\log6)(1+\log(6y))\}.
\]

**Nonzero shifts.** Choose any four row types \(i,j,k,l\), write \(A=ij,\ B=kl\) in the next estimates, and let \(Y=\sqrt{T/(2\pi)}\). The physical products are \(Aab,\ Bcd\) with \(a,b,c,d\le Y\). In each product use as first variable the residue restriction of smaller density, giving densities \(\alpha=\min(\delta_i,\delta_j),\ \beta=\min(\delta_k,\delta_l)\), where \((\delta_1,\delta_2,\delta_3,\delta_6)=(1/3,1,1/2,1)\). Drop the residue conditions on \(b,d\). Every remaining one-variable count through \(t\) is at most \(\delta t+1\).

For fixed \(a,c\), the difference \(h=Aab-Bcd>0\) must be divisible by \(g=(Aa,Bc)\). At any such shift there are at most \(1+Yg/\max(Aa,Bc)\) possible \((b,d)\). Summing against \(1/h\) through \(36Y^2\) gives
\[
 (1+\log(36Y^2))\left[\frac{1}{g}+\frac{Y}{\max(Aa,Bc)}\right].
\]
For the first term use \(g\ge(A,B)\) and at most \((\alpha Y+1)(\beta Y+1)\) admissible \(a,c\). For the second term, each positive decreasing sum over \(a\), respectively \(c\), is at most its integral on \([0,Y]\) against \(\alpha\,dt+\delta_1(dt)\), respectively \(\beta\,dt+\delta_1(dt)\). Here \(\delta_1(dt)\) denotes unit point mass at 1. The two-dimensional continuous integral equals
\[
 \int_0^Y\!\int_0^Y\frac{dx\,dy}{\max(Ax,By)}
 =Y\frac{2+|\log(A/B)|}{\max(A,B)}.
\]
Each of the two one-dimensional cross integrals costs at most \((1+\log(36Y))/A\) or \((1+\log(36Y))/B\), with the respective densities. The point mass pair contributes \(1/\max(A,B)\). Thus the weighted sums for these types together are at most \(Y^2(1+\log(36Y^2))\) times
\[
 \frac{(\alpha+1/Y)(\beta+1/Y)}{(A,B)}
 +\alpha\beta\,\frac{2+|\log(A/B)|}{\max(A,B)}
 +\frac{(\alpha/A+\beta/B)(1+\log(36Y))+1/\max(A,B)}{Y}.
\]
Each expression containing \(1/Y\) can be evaluated at \(Y_0=\sqrt{e^U/(2\pi)}>36\). The code sums the displayed expression over all 256 ordered row choices and applies the factor 4 for the two orientations and the exponential-integral bound. The additive kernel term \(1/(2\sqrt{mn})\) costs at most \(16Y^2(1+2^{-1/2})^4(1+3^{-1/2})^4\), by summing the absolute weights over the four row types. The same diagonal integration, polynomial normalization, and Riemann–Siegel error as above apply with \(\sup |E_6|\le(1+2^{-1/2})(1+3^{-1/2})\).

## Retaining the weighted fourth harmonic

For \(P=2,6\), let \(E=E_P\), let \(D\) be the original unsieved Riemann–Siegel sum and set \(z=e^{i\vartheta_0}D\), where \(\vartheta_0=(t/2)\log(t/(2\pi e))-\pi/8\). By the [theta approximation used on the critical line](../../round3/critical/PROOF.md), \(|\zeta E|\le2|E||\Re z|+3\sup|E|t^{-1/4}\) at \(t\ge200\). Put \(B=\int_{200}^T|E|^4|z|^4\), \(H=\int_{200}^T |E|^4 z^4\). The identity for \((2\Re z)^2\) and the \(L^2\) triangle inequality give
\[
 \left(\int (2|E||\Re z|)^4\right)^{1/2}\le2\{\sqrt B+\sqrt{(B+|H|)/2}\}.
\]
The original phase \(\vartheta_0\) is retained, so the harmonic contains \(|E|^4\).

Expand \(|E|^4=\sum_r c_r e^{it\log r}\). For a given \(p\mid P\) the absolute local coefficients for exponents \(-2,-1,0,1,2\), respectively, are \(b^2,2b(1+b^2),1+4b^2+b^4,2b(1+b^2),b^2\), where \(b=p^{-1/2}\). Distinct exponent tuples yield distinct positive rational \(r\).

The phase of a quadruple in the \(r\)-term has increasing derivative \(\log(r y^4/\prod n_i)\), \(y=\sqrt{t/(2\pi)}\). For \(r\ge1\) the fourth-harmonic bound \(64T\) in the unfiltered proof applies unchanged. Also for \(r>1\) the lower bound \(\log r\) gives \(32Y^2/\log r\) for all quadruples together.

For \(0<r<1\), choose an integer \(C>1/r\). On the part where some \(n_i\le y/C\), the derivative is at least \(\log(Cr)>0\). Each fixed tuple has one time interval satisfying this extra restriction because it is equivalent to \(t\ge2\pi(C\min n_i)^2\). The cost is at most \(32Y^2/\log(Cr)\). On the remaining part all four indices belong to \((y/C,y]\). The corresponding oscillatory integral is bounded by the fourth moment of this moving short-band sum. Its diagonal at a given \(t\) is at most
\[
 2H_{C-1}^2\{\zeta(2)+(\log C)(1+\log Y)\}.
\]
Indeed in the \(g,j,r',s'\) parametrization the two inner harmonic sums have ratio at most \(C\), hence mass at most \(H_{C-1}\) by the same interval argument as for \(H_5\). The remaining harmonic pair has \(r'\le s'\le Cr'\) up to exchange. For the off-diagonal use the shifted-product argument for \(A=B=1\) from the preceding section without residence restrictions. Summing \(1/g\le1\) over \(a,c\) costs at most \(Y^2\), and \(\sum_{a,c\le Y}1/\max(a,c)\le2Y\). This gives the complementary off-diagonal bound \(Y^2\{12(1+2\log Y)+16\}\). The time set is still one interval per fixed tuple. Thus each summand in \(|H|/(T\log^4T)\) has an explicit upper bound using only nonnegative multiples of \((\log T)^{-3}\) and \((\log T)^{-4}\), after using \(\log Y\le(\log T)/2\). The code evaluates it at \(U\), minimizes over five admissible integers \(C\), then sums using the absolute Fourier coefficients. Combining with the preceding bound on \(B\) proves the option \(\texttt{phased=True}\). For \(P=2,\ U=49\) the resulting fourth-moment coefficient is below \(0.014074845\).
