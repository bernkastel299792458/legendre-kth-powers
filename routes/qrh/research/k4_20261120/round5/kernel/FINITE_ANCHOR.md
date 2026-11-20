# A compact bridge into the certified fourth-power half-line

Under QRH(7/8) and the analytic inputs of the [existing half-line proof](../spectrum/PROOF.md), the open interval $(x,x+4x^{3/4})$ contains a prime for every **$\log x\ge162.3$**. The compact interval from $162.3$ through $167.4$ has full normalized error below **.999724**. The existing half-line begins at the included right endpoint. Consequently every pair of consecutive fourth powers with $n\ge418{,}310{,}343{,}281{,}874{,}847$ has an intervening prime. This bound uses no finite-rectangle count conjecture.

~~~sh
python -B round5/kernel/finite_anchor.py
~~~

The default calculation uses the five triples $(.92,9.5,-3.5),(1,9.25,-3.5),(1.1,8.75,-3.5),(.96,9.5,-3.65),(1.04,9,-3.4)$, short-core length $2^{21}$, and real nodes spaced $.001$ before taking a convex subsequence. It incorporates the [residue-filtered diagonal](../left/UNIT_DIAGONAL.md) and [shift-split off-diagonal](../left/OFF_FOURTH.md) in the short-core critical-line bound, rounding its lower logarithmic height down to a multiple of $10^{-6}$ when sharing a uniform coefficient. Keeping only the shift-split improvement certifies the bridge from $163.3$ with total below .993168; its replay is `python -B round5/kernel/finite_anchor.py --anchor 163.3 --no-unit`. The older fourth-moment bound independently certifies the entire bridge from $165.85$ with total below .997513, using the same triples and real nodes spaced $.0005$. Its replay is `python -B round5/kernel/finite_anchor.py --anchor 165.85 --step 1 --no-off --no-unit --cells 16`.

The [bridge checker](finite_anchor.py) uses 160-bit Arb, the same finite arithmetic for the short Möbius core as the previous half-line, and the following compact-height bounds. The final prime assertion uses the same elementary prime-power estimate and trivial-zero sum as in that proof.

## Spectral ranges on a compact interval

Put $d(L)=\log(1+4e^{-L/4})$, $L_0=162.3$ and $L_1=167.4$. Freeze the damping allowance of the [nonnegative polygon weight](PROOF.md) at $d(L_0)$. Push ordinates of spectral jumps below $1.45$ to $1.45$. Group the resulting finite jumps by the consecutive endpoints $1.45,2,4,8,16,64,192$, placing a jump exactly at a shared endpoint in the earlier group. The residual term of mass $r$ has density $2r\,192^2 y^{-3}$ above $192$ and is a seventh group. For a finite group $[y_-,y_+]$ all effective heights $t=y/d(L)$ satisfy

$$
 U=\log(y_-/d(L_0))-10^{-7}<\log t<
 V=\log(y_+/d(L_1))+10^{-7}.
$$

The continuous last group uses the same lower endpoint with no finite upper bound. All heights exceed verified RH height, as the checker verifies.

For each finite group and each chosen triple $(\delta,W,\log h)$, divide $[U,V]$ into equal cells of length at most $1/2$. Apply the [joint short-polynomial estimate](../left/SHORT.md) on each closed cell, with its actual upper endpoint in the harmonic subtraction and signed constant term. The largest cell coefficient gives a single $K_1$ for the group. For the right coefficient, the exponent $e=2\delta/\log t$ belongs to $[2\delta/V,2\delta/U]$. Apply the 128 [certified Mellin and local-energy cells](../spectrum/verify.py); every cell with upper endpoint smaller than the indicated lower bound for $e$ can be skipped. The largest retained upper bound yields $K_3$. Closed cells include all equality cases. On the infinite group the original all-height moment routine supplies both bounds, using eight short-core cells and a terminal half-line.

## Complete detector bounds and monotonicity

At an auxiliary abscissa $s$, set $p=3(1-s)/(2-s)$, $c=3\delta/(2-s)$ and $k=3\delta(2s-1)/(2-s)^2$. The inherited uniform bound for a cumulative distance is

$$
 B_s t^p(\log t)^{1+p}+ E_c+E_s\log t,\qquad
 B_s=\frac{c_\nu {\cal N}^{\nu_{\max}}K_3(K_1/K_3)^p}{2\pi}
       \exp\!\left(\frac{k(U+\log(UK_1/K_3))}{U+c}\right).
$$

The checker verifies $c+1+c/U<\log(UK_1/K_3)$ separately for each triple. Here the detector exponent $\nu$ increases with $\log t$. Its maximum is calculated at $V$ if finite, and at infinity otherwise. In radial mode select the best of the [simple- or triple-root polynomials](RADIAL.md), ensuring a single polynomial works on the entire exponent interval. Outside the table use the previously proved bounds. The new polynomials fit inside the original outer-circle and vertical-edge allowances after dividing by their guaranteed multiplicities. The program adds the edge terms for a triple before taking the minimum over different triples; thus each candidate includes the edge charges for its own detector and mollifier.

For each group, let $\mu$ be its positive spectral measure and $\Lambda_s(t)$ the actual cumulative positive-part moment. The function $s\mapsto\int\Lambda_s(y/d(L))\,d\mu(y)$ is convex. The algorithm selects a subsequence of real knots using the minimum complete upper bound just described, including the endpoint $7/8$ where the true moment is zero. The adjacent chord formula uses these knots and its coefficients are positive. The spectral power-log moment at the anchor is bounded by writing $u=\log(4/d(L_0))$, $z=\log(y/4)$ and $(u+z)^r\le u^r e^{rz/u}$. For the last group's density this gives the factor $2/(2-p-r/u)$ at $y=192$; its denominator is checked strictly positive.

For each selected pair of consecutive knots with right endpoint $s'$, the checker verifies

$$
s'-1+2/L_0+p/4+(1+p)/(4U_{\min})<0,\qquad
s'-1+2/L_0+1/(4U_{\min})<0 .
$$

They bound the logarithmic derivatives of the chord increment times each respective positive moment term for all $L_0\le L\le L_1$. Indeed $(\log (y/d(L)))'<1/4$, every $\log(y/d(L))\ge U_{\min}$ and the argument applies pointwise in $y$ before integration. For a row at which several competing detector bounds are close, each complete choice remains valid and its contribution is at most its own anchor majorant. The positive base term and the prime-power and trivial-zero contributions have the same decreasing bounds as in the previous half-line calculation. This transfers the scalar strict inequality at $L_0$ to the entire closed bridge; no dyadic truncation of the zero sum is needed.

2026-11-20. Project AI authors Claude and Codex. Codex derived this bridge and verified its numerical bounds.
