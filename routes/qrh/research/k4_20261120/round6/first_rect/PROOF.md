# The first geometric rectangle with a locally frozen dual AFE

Let \(H=3000175332800,\ W_*=He^{1/4},\ D=\lceil W_*-H\rceil=852126049035,\ R=D/2,\ C=H+R,\ U=\log R\). The upper integer height includes the required closed upper edge. Finite-height RH gives \(N_{>\sigma}(H)=0\) for the real parts studied here. The sufficient benchmarks are \(6(\log W_*)W_*^{3(1-\sigma)/(3\sigma-1)}\). The [previous bounds at the same height](../../round5/low/FIRST_BOX.md) and the [finite-height target](../../round5/spectrum/DENSITY_TARGET.md) specify the existing input and the interpretation.

The mean integrals here are all **one half** of a full-axis integral against \(G(t)=\min(1,(1.01R/|t-C|)^{2048})\). Each Littlewood count still charges both horizontal edges and retains the factor 2 from the full-axis interpolation. The local real-variable arguments below and the imported analytic estimates are handwritten, with their scalar bounds certified by interval and finite integer arithmetic.

## Projected AFE on individual time cells

For a squarefree \(q\), the Euler-filtered AFE at \(s=1/2+it\) has forward coefficients \(v_f(n)=\mathbf1_{(n,q)=1}\), dual coefficients \(v_d(n)=c_q(n)\) (the Ramanujan sum), and a factor of modulus \(q^{-1/2}\) on its dual sum. At each time its physical cutoffs \(x,y\) need only satisfy \(xy=qt/(2\pi)\) with \(x,y\ge q\). The remainder is explicit, including when cutoffs are integral. These statements follow by applying the asymmetric AFE for each divisor of \(q\), with the same global phase. The elementary phase version uses \(e^{-it\log(qt/(2\pi e))+i\pi/4}\) after combining the dual Euler terms. [Simonič, Theorem 4, Corollary 1 and Table 2](https://arxiv.org/pdf/1910.08274#page=4) · [Periodic AFE and diagonal bound](../phase/PERIODIC_FOURTH.md)

Put \(J=1.012(1.01)R\). The tail \(|t-C|>J\) uses the uniform cumulative fourth moment in that periodic AFE proof and the [translated power-tail bound](../../round5/low/NARROW_COVER.md). Divide the remaining time interval into equal cells of center \(c\) and half-length \(j\). At \(t=c\) put \(x_0=a\sqrt{c/(2\pi)},y_0=b\sqrt{c/(2\pi)}\), \(a=\alpha\sqrt q,\ b=q/a\). Within the cell set
\[
 x(t)=x_0(t/c)^p,\qquad y(t)=y_0(t/c)^{1-p},\qquad 0\le p\le1 .
\]
Their product has the required value. For \(p=1\), the dual sum on this entire cell is one fixed Dirichlet polynomial. The forward cutoff is linear in \(t\). The AFE remainder multiplier using \(a\) instead of its actual value is increased by at most \((1-j/c)^{-|p-1/2|/2}\). The program checks the actual lower bounds on all cutoffs and \(t>1000\).

For either frozen branch let \(Y=\lfloor x_0\rfloor\) or \(\lfloor y_0\rfloor\), and let \(b_n\) be its real periodic coefficient, cut to \(n\le Y\). The square of its Dirichlet polynomial has two coefficient norms. The harmonic norm uses the positive gcd-class diagonal from the [periodic AFE proof](../phase/PERIODIC_FOURTH.md) at \(\log Y\). The unweighted norm \(\sum_k(b*b)(k)^2\) is bounded by
\[
 \sum_{v\mid30030}\mu(v)\sum_{i,j\le Y/v}
   \left(\sum_{k\le Y/(v\max(i,j))} b_{vik}b_{vjk}\right)^2 .
\]
Indeed the exact expression requires \((i,j)=1\); imposing only coprimality to \(30030\) on their common divisor enlarges a sum of squares. For \(\max(i,j)=i\) the inner sum is periodic with modulus \(q\) and its length is independent of the smaller index \(j\). Group \(j\) by residue, count each ordered pair twice except for the diagonal, and evaluate with signed integers. For each \(v\) the absolute sum is at most \(2\max|b|^4Y^2(1+\log Y)\), as the \(i\)-th row before symmetry has size at most \(\max|b|^4Y^2/i\). The 64-bit guard uses the larger \(1+\operatorname{bitlength}Y\). The forward product indices are units modulo \(q\), allowing the existing folded norm for \(q=6,30\). Dual product indices use the unrestricted scalar fold. All these time folds permit arbitrary complex phases from the translation. [Periodic fixed Gram calculation](periodic_local.py)

On a varying side, its difference from the frozen polynomial is a moving initial or final portion of an integer interval \([A,B]\) on each half of the time cell. Each fixed quadruple in the expansion of the fourth norm has time support one interval. Put \(w(n)=|b_n|\) before the cutoff. The exact positive equal-product energy contains the trivial swaps
\(2(\sum_{A\le n\le B}w(n)^2)^2-\sum w(n)^4\). For the others write the four indices as \(gr,hs,gs,hr\), with coprime \(r>s\) and \(g\ne h\). Necessarily \(r\le B-A\), \(r-s\le \lfloor r(B-A)/B\rfloor\), and \(A/s\le g,h\le B/r\). Sum the nontrivial terms with their two symmetric orientations. For one \((r,s)\), the weight of distinct \(g,h\) is exactly \((\sum_g w(gr)w(gs))^2-\sum_g w(gr)^2w(gs)^2\). Both one-dimensional sums are periodic and exact. The implementation bounds the 64-bit accumulators by \(2\max(w)^4(B-A+1)^3\), since three product indices determine the fourth and all terms are positive. For unequal product frequencies, the shift-correlation sum is at most this same energy by Cauchy. The allowed shifts in the forward branch are even. Thus the scalar per-energy cost on a half-cell of length \(j\) is at most
\[
 j/A^2+2\sum_{1\le h\le (B^2-A^2)/g}
       \min(j/A^2,2B^2/(g A^2 h)),
 \qquad g=2\text{ forward},\quad g=1\text{ dual}.
\]
Both halves are added and divided by two. This can also be replaced by the pointwise count of \(w(n)\) on the prefix. [Periodic short-interval multiplicative energy](prefix_energy.py)

## The mixed harmonic on a translated cell

Write the two positive frequency polynomials as \(A(t),B(t)\), absorb \(q^{-1/2}\) into \(B\), and put \(\phi=t\log(qt/(2\pi e))-\pi/4\). To control \(\tfrac12\int_{t_1}^{t_2} e^{2i\phi}A(t)^2B(t)^2dt\), use the [upward contour for the paired AFE](../phase/SMOOTH_PHASE.md) separately on each open segment with fixed integer cutoffs. Here \(t_1=c-j,\ t_2=c+j,\ h=\sqrt{t_2}\). Let \(X_k^-,X_k^+\) be the minimum and maximum physical cutoff of each branch, let \(m_k,D_k\) denote the mean and interval discrepancy of its unnormalized absolute coefficients, and put
\[
 M_k=m_k+D_k/\sqrt{X_k^-},\qquad d=\max_k D_k/(m_k X_k^-),\qquad
 I_n=\int_0^h[(v+1/2)^{-1}+d]^n\,dv .
\]
At imaginary shift \(v\ge0\) the exponential provides \((q t/(2\pi))^{-2v}\), sufficient to divide each of the four sums by its physical cutoff to the power \(v\). The normalized branch sum is bounded by \(M_k\sqrt X[(v+1/2)^{-1}+d]\) using interval discrepancy and partial summation. Since \(xy=qt/(2\pi)\), the top contour costs at most \(K(t_2^2-t_1^2)[(h+1/2)^{-1}+d]^4/2\), and the two outside vertical contours cost at most \(K(t_1+t_2)I_4\), where \(K=M_f^2M_d^2/(2\pi)\). At a jump of branch \(k\), one changes its square by at most twice its new coefficient times the full absolute sum. Its total edge cost is bounded by
\[
 \frac{2 I_3}{q}\sum_{k\ {\rm moving}}M_k M_\ell^2 X_\ell^+
        \big(m_k(X_k^+-X_k^-)+D_k\big),\qquad \ell\ne k .
\]
Simultaneous jumps can be telescoped before applying that bound. The constant branch incurs no jump. Halve the sum of the top, outside and jump contributions to obtain \(B_{\rm mix}\). If \(F,D_0\) are the two upper fourth *roots* on this half-cell measure, the identity for the real part of \(e^{i\phi}AB\), Cauchy and Minkowski give the upper fourth root
\[
 \big(F^2+D_0^2+\sqrt{2(F^2D_0^2+B_{\rm mix})}\big)^{1/2}.
\]
The ordinary \(F+D_0\) is also allowed. Add the AFE remainder before taking the fourth power. [Local mixed harmonic](local_harmonic.py)

## Local short detector and its first moment

Put \(P=E_{210}\sum_{n\le N,(n,210)=1}\mu(n)\omega_N(n)n^{-s}\), with the same finite step weights as the [earlier joint second mean](../../round5/left/SHORT.md). On \([C-J_1,C+J_1]\), \(J_1=1.02(1.01)R\), the old diagonal at the true Riemann–Siegel height \(y(t)\) costs at most
\[
 J_1\big[A_+(\log y_++\gamma)+B_++G/y_-\big]
\]
on the half-interval measure, with the same \(A,B,G\) as there. Every off-diagonal pair is supported on one interval, so half the prior shift bound at the upper height works. On the complement use the cumulative short second mean times the power tail. This already proves the direct, translated short norm.

For the signed first moment, the old contour on \(\Re s=1/2,2\) gives cumulative error at most \(20(1+\|\lambda\|_{-1/2})\sqrt t\) for \(t\ge200\). A uniform alternative is \(160(1+\|\lambda\|_{-1/2})(t+4)^{1/4}\). Indeed \((s-1)\zeta(s)/((s+1)(s+2)^{1/4})\) is bounded by 48 on both vertical lines and hence throughout the strip by the maximum principle for functions of polynomial growth. On the critical line for \(|t|\le200\), truncate Euler summation through \(N=\max(1,\lceil |t|\rceil)\); the finite sum, pole and integral together cost at most \(8\sqrt N\). Dividing by \(|s+2|^{1/4}\) gives a bound below 48. For \(|t|>200\), use the symmetric explicit Riemann–Siegel inequality. The line 2 follows by absolute convergence. For \(t\ge2\), \(|s+1|/|s-1|\le2\), so the two horizontal edges in the cumulative contour, after halving, cost at most \(144\|\lambda\|_{-1/2}(t+4)^{1/4}\). The pole and absolutely convergent right edge fit in the stated 160. For \(t<2\) the critical-line Euler bound suffices directly. Apply the cumulative bound at \(C+V\) and \(|C-V|\), using evenness of the real part, then halve and average. Jensen on the fourth root gives the translated first-moment error used by the code. [Translated joint moments](local_short.py)

The critical mollifier for an absorbed \(E_{q_0}\), \(q_0=6,30\), is \(E_{210/q_0}C_{210}\). A multiple \(\theta P\) can be subtracted on its flat coefficient head. For each \(d\mid 210/q_0\) the harmonic reduction is \((2\theta H_1-\theta^2 H_2)/d\) with the certified \(H_1,H_2\) from the short-core arithmetic. All changed indices are in the first folded regime. Both the affine and localized bounds retain a harmonic coefficient at least \(1.01(1-1.03^{-2047})R\) there. Every remaining weighted square sum decreases. Minkowski splits the full detector into the residual fourth/second-moment term and \(\theta\zeta P-1\). The latter uses the translated second moment, as well as the signed first moment with its actual coefficient \(-2\theta\). This produces the \(4/3\) norm used in each actual rectangle.

## Periodic off-diagonal bound for the joint second moment

One can compute the same \(\zeta P\) with the periodic AFE at \(q=210\) before multiplying by its short core \(\sum a_d d^{-s}\). All \(d\) in the core are units. Thus in either branch \(\tau(ru)=\tau(r)\) for \((u,210)=1\), where \(\tau\) is the raw periodic coefficient. In the forward product one compares frequencies \(dm,en\); the dual product has ratios \(m/d,n/e\), giving the same comparison with \(d,e\) exchanged. Write \(s=(d,e)\). The equal-frequency sum uses the single harmonic inner sum \(H_{\tau^2}(y s/\max(d,e))\) divided by \([d,e]\). Its leading term and constant are given by the periodic harmonic formula. Its error can use \(E/x\), \(E=\max(2D_{\tau^2},\rho_{\tau^2}/\exp(1)+|c_{\tau^2}|)\), also for \(0<x<1\). The signed finite values
\[
 A=\sum a_da_e/[d,e],\qquad B=-\sum a_da_e\log(\max(d,e)/s)/[d,e]
\]
are rounded outward. In the implementation each \(a_da_e/[d,e]\) is rounded toward zero with denominator \(2^{42}\), then the \(A\) and \(B\) upper bounds add \(K^2/2^{42}\) and \(K^2\log N/2^{42}\), \(K\) the number of nonzero core coefficients. The exact unsigned gcd harmonic expansion is bounded by \((1+\log N)^3\), giving the signed integer guard.

For positive shift \(dm-en=sv\), the two varying indices run in a progression of length at most \(ys/\max(d,e)\). Its raw absolute weights can be written \(|\tau(u)\tau(u-v)|\) on an arithmetic progression of unit step modulo 210 after scaling by the fixed outer indices. On an arbitrary interval in the integer parameter this sequence has a residue-dependent mean \(\rho_v\) and upper discrepancy \(d_v\). The code checks every unit step modulo 210; translations only rotate the period. For either of these nonnegative sequences, its sum against \(1/v\) through \(NY\) is bounded by its mean times \(\log(NY)\) plus the explicit 16-term residue-wise integral remainder from the [periodic off-diagonal proof](../phase/PERIODIC_FOURTH.md). Denote these two bounds by \(L_\rho,L_d\). Then the half-integral's off-diagonal is at most
\[
 2 L_d(\sum |a_d|)^2+
 2 L_\rho Y\sum_{d,e}|a_da_e|/\max(d,e)
 +.118\left(\sum_d |a_d|/\sqrt d\right)^2
       (2\overline{|\tau|}\sqrt Y+D_{|\tau|})^2.
\]
Here \(1/s\le1\) only in the discrepancy component, and the .118 contribution counts both orientations in the unrestricted square. The AFE remainder is multiplied by the actual short polynomial. Its half-mean square follows from the unrestricted folded mean using its two explicit coefficient norms. [Projected joint second moment](projected_short.py)

The fixed-exponent right-boundary choices and the angular rather than maximum-modulus Jensen estimate are from the [preceding translated certificate](../../round5/low/NARROW_COVER.md). The extra right-boundary choice takes the single applicable Mellin exponent cell and applies the centered affine fold to the whole low and high norms, before taking the minimum with the local energy choices. The count at \(\sigma\) is at most \(\sum(\beta-s)_+/(\sigma-s)\) for each tested \(s<\sigma\). The finite real-part search only selects which certified upper bounds to use. [Combined five-node verifier](first_bounds.py)

## Directed harmonic Gram on the frozen prefix

Let \(N\) bound the integral cutoff \(y\). In each branch put \(w(n)=1_{(n,q)=1}\) or \(c_q(n)\) before any \(q^{-1/2}\) factor. The earlier harmonic diagonal equals
\[
 \sum_{(i,j)=1}\frac{1}{ij}\left(\sum_{l\le y/\max(i,j)}
                 \frac{w(il)w(jl)}l\right)^2 .
\]
Enlarge the sum to \((i,j,210)=1\), put \(n=\max(i,j)\le N\), and group by \(h=(n,210)\), \(k=(\min(i,j),q)\). Retain only \((h,k)=1\). The inner sequence depends only on \(h,k\). An absolute upper bound for all prefixes up to \(\lfloor N/n\rfloor\) gives a uniform bound for every \(y\le N\). It is essential to take the running maximum for the signed sequences. Those signed sequences have zero period mean, checked for every pair of classes. Compute the first 1024 prefixes and bound the remaining ones by \(|c|+E/1024\) using the period harmonic constant \(c\) and its certified \(E/m\) remainder from the [periodic AFE proof](../phase/PERIODIC_FOURTH.md). The unsigned inner sequences are nonnegative and only need their largest given prefix.

For fixed \(n,h,k\), the outer prefactor is \(n^{-1}\) times twice the harmonic sum of \(j<n\) with \((j,h)=1,(j,q)=k\), plus \(n^{-1}\) inside the parentheses if \(h=k=1\) to count \(j=n\). Both the outer and inner periodic sequences depend only on the gcd of their argument with \(210\) or \(q\). By divisor inversion write each as \(\sum_{d\mid n}\theta_d\) with integer coefficients. For \(S=2^{40}\), let \(J(m)=\sum_{j\le m}\lfloor S/j\rfloor\) in exact signed 64-bit arithmetic. An integral approximation to the harmonic prefix through \(m\) is
\[
 \sum_d\theta_d\left\lfloor\frac{J(\lfloor m/d\rfloor)}d\right\rfloor.
\]
Its difference from the exact prefix multiplied by \(S\) is at most \((m+1)\sum_d|\theta_d|\). The loops add this error explicitly. The guards bound all integer intermediates before floating-point conversion. Every subsequent summand is nonnegative. Each incurs fewer than ten binary64 operations or conversions, followed by at most \(N\tau(q)\) positive additions; the guard \((N\tau(q)+100)2^{-52}<2\cdot10^{-7}\), and the final factor \(1+10^{-6}\), cover their aggregate roundoff by the ordinary multiplicative floating-point error bound. Positive computed quantities here are normal numbers; the zero bounds are exact or rounded upward by the added arithmetic guard. No fast-math option is enabled. The code exhausts every \(y\le32\) against direct rational summation for both branches at \(q=6,30\). [Finite harmonic verifier](exact_harm.py)

## Joint positive Gram of the two fixed polynomials

On any fixed-dual cell write \(F=F_0+E,\ B=B_0\), with both subscript-zero polynomials frozen at the midpoint. In the product \(F_0B_0\) the equal-frequency terms have forward indices \(ir,is\) and reverse indices \(js,jr\) with \((r,s)=1\). Consequently \(i,r,s\) are units modulo \(q\), and the reverse weight in the Gram is \(c_q(j)^2\). In the unweighted form, with forward cutoff \(f\), reverse cutoff \(d\) and \(m=\max(r,s)\), the inner weight is exactly
\[
 U(f/m)C(d/m),\qquad
 U(x)=\sum_{n\le x}1_{(n,q)=1},\quad C(x)=\sum_{n\le x}c_q(n)^2 .
\]
In the harmonic form the same two prefixes contain an additional \(1/n\) and the outer pair carries \(1/(rs)\). All terms are positive. As in the directed harmonic bound, relax coprimality of the outer pair to \((r,s,210)=1\). When \(r=m,\ h=(m,210/q)\), the smaller index runs over units coprime to \(h\); the diagonal \(r=s\) is now present only for \(h=1\). The [fixed mixed Gram calculation](frozen_mix.py) accumulates exact integer counts and positive binary64 harmonics. Every unweighted accumulator is at most \(2\max|c_q|^2 f d(1+\operatorname{bitlength}\min(f,d))\) by summing the positive outer rows. The guard \((6\max(f,d)+100)2^{-52}<10^{-7}\) covers all positive harmonic accumulations and conversions with the final factor \(1+10^{-6}\).

A time fold on the unrestricted product indices, divided by \(q\), bounds \(\tfrac12\int |F_0B_0|^2\le Z_0\). Hölder then gives
\[
 Z:=\tfrac12\int|F B|^2\le
 \big(\sqrt{Z_0}+\|E\|_4\|B\|_4\big)^2,\qquad
 Z\le \|F\|_4^2\|B\|_4^2.
\]
Here the norms all use the half-interval measure. Before adding the explicit AFE remainder the fourth-root upper bound can therefore also use
\[
 \left[\sqrt{\|F\|_4^4+\|B\|_4^4+2Z}
            +\sqrt{2(Z+B_{\rm mix})}\right]^{1/2}.
\]
This is optional in each cell; for \(q=6,\alpha=1.25\) with eight cells on the first geometric rectangle, the original Cauchy alternative gives the same numerical bound to displayed precision. Its complete half fourth moment is below \(1.7670704170\cdot10^{15}\).


## Five counts on the actual rectangle

At the height \(He^{1/4}\), finite RH up through \(H\) permits use of just the translated rectangle. The table gives strict upper bounds both on its actual counts and on the ratio to the benchmark defined at the start. In the fixed-\(e\) right-boundary Mellin calculation only the last cell of a 65536-cell grid is needed. Its other input restrictions hold here.

| \(\sigma\) | Benchmark rounded up | Count strictly below | Upper bound divided by benchmark | Selected hinge \(s\) |
|---:|---:|---:|---:|---:|
| .800 | 43065067 | 243733500 | 5.660 | .7835 |
| .820 | 7856651 | 70533811 | 8.978 | .8032 |
| .837 | 2057409 | 24420595 | 11.870 | .8219 |
| .852 | 678490 | 9064416 | 13.360 | .8371 |
| .865 | 272893 | 3815142 | 13.981 | .8502 |

For reproducibility at 192-bit Arb precision run the following from the directory containing the round folders. The four parameter triples and the five strict upper checks are explicit in the driver. These bounds use no assumptions about the unverified zeros besides the hypotheses already stated; they do not meet any of the five benchmark counts. The weighted combination at lower heights instead gives the [continuous low-end extension](LOW_JOIN.md).

~~~powershell
python -B round6/first_rect/first_bounds.py
~~~
