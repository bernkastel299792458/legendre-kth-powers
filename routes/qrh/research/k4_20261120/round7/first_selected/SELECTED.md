# Actual count at the selected node \((5,.854)\)

Let \(H=3000175332800,\quad t_*=He^{5/4},\quad T=\lceil t_*\rceil=10471640843990\). Finite RH through \(H\) equates the count above .854 on \((H,t_*]\) with its cumulative count. Enlarging the upper height to \(T\) preserves an upper bound. The sufficient integer cap supplied by the outer reduction is 805224. The scalar estimates in this note use finite RH, not additional information about zeros above \(H\).

## Moving all the boundaries

For a positive window \((b,b+D]\), take \(R=D/2,\ C=b+R,\ U=\log R,\ v=1.01,\ M=2048,\ \bar v=vM/(M-1)\) in the [translated Littlewood proof](../../round5/low/MOVING_WINDOW.md). The radial mixture is \(\min(1,(vR/|t-C|)^M)\). The two Dirichlet coefficient means at the right and left polynomial boundaries are invariant under translation, since translating the time variable multiplies fixed coefficients by phases. Use their own \(U\), exponent \(e=2\delta/U\), head \(Y=Re^{\ell_h}\), and \(X=Ye^W\) in **each** window.

Let \(B=C+vR,\ p=1+k/\log B\). If the symmetric integrand is even and its cumulative integral over \([0,x]\) is bounded by \(c x\log^k x\) for every \(x\ge B\), the full-axis integral divided by two against this window is at most
\[
  \frac{c B\log^k B}{2}\frac{M}{M-p}
       \{1+(vR/C)^{M-p}\}.
\]
This is the [centered power-tail estimate](../../round5/low/NARROW_COVER.md) with arbitrary center. Indeed a mixture interval \([C-t,C+t]\) has a second copy of the cumulative bound only when \(t>C\), and \(C+t\le B t/(vR)\) for \(t\ge vR\). The \(k=4\) choice uses the [paired centered AFE moment](../../round6/phase/CENTERED_PHASE.md) for \(\zeta E_{210}\). The companion critical-line polynomial mean uses the [nested residue folds](../../round6/folds/FOLD_MEAN.md), including their diagonal coefficient on the small-core frequencies. The short-detector split and signed first moment from the [first geometric rectangle](../../round6/first_rect/PROOF.md) remain valid with \(C\) replaced everywhere, including the two power tails. At modulus 210 the translated joint second moment also uses its local two-branch AFE on \([C-1.02vR,C+1.02vR]\); its cumulative alternative uses the preceding \(k=1\) formula.

On each upper or lower horizontal edge the outside Jensen circles have radius \(1.44,1.58,1.72,1.86,1.96\) and are split into 96 angular cells using the minimal real part of the cell. Euler summation now uses the actual upper height \(b+D+7\), the lower denominator \(b-2\), the actual \(X,Y\), and all primes of the chosen squarefree sieve modulus \(Q\). The right vertical divisor contribution is \(D[2(\log Y+2)/Y]^2/\pi\). The proof retains **both** edge terms of every constituent rectangle. The driver takes the better of finitely many real-part hinges for each interval before summing. An endpoint can be approached from outside for a cumulative bound; counting a zero at a shared closed edge twice would still be an upper bound.

With modulus \(Q=210\), base 210, \((\delta,W,\ell_h)=(.85,8.5,-2.8)\) and core 131072, the following centered results use the exact upper integer height. The full-range test also permits core 262144.

| Number of equal height windows | Separate count bounds (rounded up) | Bound on the sum (rounded up once) |
|---:|---|---:|
| 1 | 17504720 | 17504720 |
| 2 | 13650773, 14221216 | 27871988 |
| 4 | 10819288, 11110111, 11361301, 11582867 | 44873566 |

For a two-window or four-window split the transferred \(R\) is smaller and the available right normalization and folded costs must be recalculated; the table records the actual results.

## Right norm at a single known exponent

The low coefficient norm uses the last of 65536 equal \(e\) cells in the [Mellin bound](../../round5/kernel/mixed_low.py). For the high coefficient norm reuse the [sieved Selberg reduction](../../round4/density/SIEVED.md) at \(s=2+e\). Let \(Z_Q(s)=\zeta(s)\prod_{p\mid Q}(1-p^{-s})\), \(D=1/Z_Q(s)\). The signed logarithmic sum in the transition equals \(-D'(s)\), computed by interval differentiation. Write
\[
 R(t)=\sum_{n>e^t,(n,Q)=1}\mu(n)n^{-s}(\log n-t).
\]
Truncate through \(N=4096\). The finite sum is continuous and piecewise affine, with breakpoints exactly at the retained \(\log n\). Its extreme values on any \([a,b]\) occur at the two ends or one of those breakpoints. Suffix sums of the signed weights and their logarithmic products enclose each such value directly. Uniformly for \(0\le a\le b\) the magnitude of the omitted tail is at most
\[
 N^{1-s}\left(\frac{\log N}{s-1}+\frac1{(s-1)^2}\right).
\]
This follows by comparison with \(\int_N^\infty (\log x)x^{-s}dx\), since each omitted nonzero term has \(0<\log n-t\le\log n\). Intersect the resulting enclosure with the earlier unconditional bound \(1.2e^{-(s-1)a}\) in absolute value. Numerical overlaps between a grid boundary and a single \(\log n\) are checked smaller than \(10^{-35}\); the finite interpolation enclosure adds \(10^{-34}\). There cannot be two such unresolved breakpoints since their distance is at least \(\log(1+1/N)\).

Use the original local Selberg integral partition in the variable \(r=\log(j/Y)\). The head \(-8\le r\le0\) has 192 cells, and the transition \(0\le r\le W\) has 512 cells; the tails follow the [direct high-norm proof](../../round4/density/DIRECT_HIGH.md). In every cell use the fixed exponent \(s\), exact \(D,-D'\) and the signed residual enclosure above. This computes \(R\,Y^e S_Q(2+e)\) as an upper bound in the prior normalization. The [verified implementation](right_fixed.py) is allowed alongside the inherited high-norm bound. The right mean can take the smaller of the centered affine fold and the [finite-band density fold](../../round5/mean/RIGHT.md), the latter evaluated in the last of 64 closed cells; for \(Q=2310\) it additionally has outer modulus 2310, inner modulus 210, and cutoff \(95R\). The q=210 and q=2310 calculations use their own coefficient norms and Euler factors throughout.

## Origin-centered cumulative comparator

Use the analytic window centered at zero with radius scale \(T\). With real coefficients and reflected ordinates the radial main term now has \(1/(2\pi)\) instead of the \(1/\pi\) in a single translated rectangle; this is the cumulative identity in the [same-height proof](../../round5/low/FINITE_POINTS.md). The code divides **both** endpoint norms by two before applying the translated formula, giving exactly the necessary factor for every interpolation exponent. It uses \(U=\log T,\ Y=Te^{\ell_h}\), the same freshly computed right norm, and the [origin-centered short detector](../../round5/left/SHORT.md) with the projected fourth moment. The vertical divisor term still has length \(T-H\). This comparator is distinct from adding bounds on constituent windows.


The verified cumulative witness at \(Q=2310\), Euler base 210, critical core 262144, \(\alpha=1,\ \delta=.96,\ W=8.5,\ \ell_h=-2.8,\ s=.8406\) gives
\[
                 N_{>.854}(He^{5/4})<13\,180\,558.
\]
Its ratio to 805224 is below \(16.369\). Fixing just these *numerical input norms* \(A_L,A_R\), the universal radial Jensen lower bound from the [detector comparison](../../round5/low/FINITE_POINTS.md) is above \(5\,507\,945\) even after dropping all positive edge terms and optimizing the hinge over the real variable. This is a floor on this family of upper-bound formulas with these inputs. The actual count could already satisfy the target. At the displayed hinge its left interpolation exponent is \(P=0.4574122069\ldots\). Keeping the hinge and detector fixed, lowering only the left bound by a factor of 450, or only the right bound by a factor of 172, would still leave the computed output above the benchmark. Indeed the positive main term scales as \(A_L^P A_R^{1-P}\), and fixed nonnegative edges only increase the required improvement factor.

From the directory containing the round folders:

~~~powershell
python -B round7/first_selected/selected.py --parts 0 --q 2310 --core 262144 --cases .96,8.5,-2.8 --check 13180558
python -B round7/first_selected/selected.py --parts 1 --q 210 --core 262144 --cases .85,8.5,-2.8 --check 17504720
python -B round7/first_selected/selected.py --parts 2 --q 210 --core 131072 --cases .85,8.5,-2.8 --check 27871988
python -B round7/first_selected/selected.py --parts 4 --q 210 --core 131072 --cases .85,8.5,-2.8 --check 44873566
~~~

All interval arithmetic uses 192 bits apart from the stated guarded finite prefix routines reused from the source proofs. Angular minimizations over finite trial radii, sieve parameters, and hinges select valid witnesses without asserting an optimum. The five-node first-height result at \(He^{1/4}\) and the continuous [low-end continuation](LOW_CONTINUATION.md) are independent of this selected count.


## A monotone prefix meeting the selected integer cap

On the actual shorter window \((H,H+800000000]\), take \((Q,\text{base})=(210,6)\), \(\alpha=5/4\), \((\delta,W,\ell_h)=(.70,7.5,-2.5)\). Use the [two-cell locally frozen dual moment](../../round6/first_rect/PROOF.md), the affine critical polynomial mean (as \(\log R<20\)), and the best among short core lengths \(512,2048,8192,32768\). The printed estimate is below \(793974.877\), giving the integer conclusion
\[
 N_{>.854}(t)\le793974<805224\qquad(H\le t\le H+800000000).
\]
This is a strict initial part of the selected rectangle. The full remaining height is over \(7.47\cdot10^{12}\) above \(H\); monotonicity alone gives no bound on its new zeros. Reproduce by

~~~powershell
python -B round7/first_selected/selected.py --prefix 800000000 --base 6 --alpha 5/4 --q 210 --core 32768 --cases .70,7.5,-2.5 --check 793975
~~~


## Strongest full-height witness in this calculation

At \(Q=2310\), base 210, core \(32768,\ \delta=1.10,\ W=8.5,\ \ell_h=-2.4,\ s=.8403\), the complete one-sided count upper bound is \(12\,736\,011.796\ldots\), strictly less than **12736012**. Its ratio to the required cap is below \(15.817\). The left and right input norm bounds are \(6.7142801\ldots\,10^{14}\) and \(0.091371286\ldots\). The universal radial floor using this particular input pair is greater than \(5\,314\,154\). At the stated hinge \(P=0.46399932\ldots\), reducing the full-height output to 805224 by changing only one endpoint norm would need an improvement exceeding a factor of 383 at the left or 172 at the right. This observation concerns the chosen moment method. It leaves the true integer count undetermined.

~~~powershell
python -B round7/first_selected/selected.py --parts 0 --q 2310 --core 32768 --cases 1.10,8.5,-2.4 --check 12736012
~~~
