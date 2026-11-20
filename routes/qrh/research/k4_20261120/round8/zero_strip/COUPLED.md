# Several Fourier harmonics on the sources of one detector

Use the hypotheses and cumulative physical formula of [COMPLETE_GREEN.md](COMPLETE_GREEN.md). For source knots \(a_0<\cdots<a_k\) choose real amplitudes \(v_{m,i}\) for finitely many positive integers \(m\), with \(v_{m,0}=0\). These amplitudes may have either sign. As in the [single-harmonic construction](MULTI_RAW.md), extend each array by the solution \(V_m''=(m\omega)^2 V_m\) between its knots, by zero on the left and by a decaying exponential on the right. Put \(d_{m,i}=V_m'(a_i+)-V_m'(a_i-)\), and choose constant source means \(b_i\ge0\). The test and its source on \(a_i\) are

\[
 \Psi(\sigma,t)=B(\sigma)+\sum_m V_m(\sigma)\cos(m\omega t),\qquad
 B(\sigma)=\sum_i b_i(\sigma-a_i)_+,\qquad
 S_i(\theta)=b_i+\sum_m d_{m,i}\cos(m\theta).
\]

Each test must be nonnegative on the **whole** detector strip, including on its extra zeros, and \(S_i\) must be nonnegative at every angle. Differentiating the hyperbolic interpolants gives the two endpoint derivatives in [MULTI_RAW.md](MULTI_RAW.md). On every knot interval \(|V_m|\) reaches its maximum at an endpoint, by the maximum principle. The first integral \((V_m')^2-(m\omega V_m)^2\) is constant, so \(|V_m'|\) also attains its maximum at an endpoint. On the right tail both decrease. Thus the angular and right edge estimates of [WEIGHTED_GREEN.md](WEIGHTED_GREEN.md) hold with

\[
 M=\sum_i b_i+\sum_m\max_i\{|V_m'(a_i-)|,|V_m'(a_i+)|,m\omega|v_{m,i}|\}.
\]

At the chosen two horizontal ordinates every sine vanishes simultaneously. Positivity of \(S_i\) gives \(|d_{m,i}|\le2b_i\) by its Fourier integral. The normalized Poisson attenuation on both source edges is at most \(10^{-6}\) for each first harmonic by the saved row assertion, and decreases with frequency. Thus the source cost is bounded by \(b_i(1+2h\,10^{-6})\) times the existing unit-weight price, for \(h\) harmonics. The factor follows by applying this bound on each of the two edges before taking the weighted geometric mean, whose exponents sum to one. Every source in a test uses the same taper and radial polynomial. Source interpolation lines can be chosen individually.

## Continuous checks

On a knot gap of length at most \(g\) and at angular frequency \(m\omega\), either hyperbolic interpolation coefficient lies between the corresponding affine interpolation coefficient times \(\alpha_m=m\omega g/\sinh(m\omega g)\) and that affine coefficient. This follows by monotonicity of \(\sinh(x)/x\). In particular a lower bound for \(V_m(\sigma)\cos(m\theta)\) is the affine interpolation of \(\min(z,\alpha_m z)\) at the two endpoints, with \(z=v_{m,i}\cos(m\theta)\); signed endpoints are allowed. For an affine physical hinge profile \(R\) this reduces the joint comparison at fixed angle to its values at the two endpoints.

On \(0\le\theta\le\pi\) use the 193 nodes \(j\pi/192\). In the present tests every zero of each \(\cos(m\theta)\) is a mesh node, as is the corner of the positive cosine at \(\pi/2\). The interpolation error on one angular cell is at most \(\pi^2/(8\cdot192^2)\) times the sum of \(m^2\) times the absolute harmonic coefficients, with 1 added for a unit cosine target when applicable. This bound applies to the piecewise minimum above because the signs are constant inside each cell. All source, real-part and angular repairs are recomputed using Arb, including the physical frequency enclosure. A proposed linear-program solution can be discarded without affecting any inequality.

## Separable candidate columns

[coupled_cone.py](coupled_cone.py) uses the common nodal shape \(v_{m,i}=c_m v_i\), with \(v_i\ge0\). On each knot interval the lower interpolation just proved uses \(\alpha_m\) for that column's gap. Use the angular grid and its curvature correction to bound \(K=\sup_\theta[-\sum_m\min(c_m\cos(m\theta),\alpha_m c_m\cos(m\theta))]\) from above. Starting from the left, increase each \(b_i\) until \(S_i\ge0\) and \(B(a_{i+1})\ge K v_{i+1}\). Hence \(\Psi\ge0\) on the whole internal knot range. To its right, the angular part and the terminal constant \(B(a_k)\) are the circular Poisson extension of the nonnegative terminal trigonometric polynomial, with Fourier multipliers \(e^{-m\omega(\sigma-a_k)}\). The remaining linear term has nonnegative slope. To its left the test is zero. The final cone combines any positive multiples of these globally nonnegative columns, repairs any angular coverage deficit using ordinary scalar hinges, and charges each selected test in full. The positive reward only needs angle \(0\) to \(\pi/2\) at this final stage, since all columns are nonnegative on the complementary portion. The even-harmonic absolute reward is invariant under \(\theta\mapsto\pi-\theta\).

## Independently variable source amplitudes

[free_green.py](free_green.py) also allows independent signed amplitudes for each pair \((m,i)\). A floating linear program proposes the \(v_{m,i}\) and \(b_i\). The verifier freezes the proposal, recomputes the one-sided derivatives and raises \(b_i\) to ensure \(S_i\ge0\) for every angle. Let the full target real-part profile be \(R=\sum_i w_i(\sigma-a_i)_+\) with \(w_i\ge0\), and let \(z(\theta)\) be the positive cosine or absolute cosine. It finds an outward bound \(\delta\ge0\) for \((Rz-\Psi)/R\) by the vertex and angular checks above. On the leftmost node both sides vanish, so division is used only at the other nodes. The verifier adds \(\delta w_i\) to the **same** detector's source means. The resulting detector then pays \(Rz\) and is nonnegative everywhere between its first and last nodes. The positive reward is checked on the entire semicircle, and in the absolute case even modes give reflection symmetry. Positivity outside the knots follows from the same Poisson extension. This method also charges its full edge constant and all its sources at each sampled height. Price proposals chosen at nearby heights or using other candidate families affect only the choice of a verified plan.

## Connected physical certificate

With the original compact spatial density, 25 closed cells cover \([138.9,139.25]\). The largest complete upper endpoint is smaller than **0.996239155504872**. This joins the 15-cell interval starting at \(139.25\) in [MULTI_RAW.md](MULTI_RAW.md). From this directory run

~~~powershell
python -Bu complete_green.py --first 138.9 --last 139.25 --pieces 25 --uniform 5 --nh 8 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016' --coupled
~~~

The independent-amplitude implementation also accepts optional extra source lines to the right of \(\Theta=7/8\). The physical target is set to zero there by QRH, and every such source still pays its complete interpolation price and edge contribution. The nodal comparison gives a nonnegative interpolation between the physical terminal reward and the zero target on the first virtual knot. After the last virtual knot, nonnegativity follows by the Poisson extension. The repair denominator on these additional knots is the positive affine continuation of the original hinge sum, so increasing the original source means by \(\delta w_i\) repairs the whole extension as well. When an exponent exceeds the archived radial range the verifier recomputes the same polynomial estimates for the upper grid, without extrapolation. With the optional tight derivative evaluation, \(\nu/\sinh(\nu h)\) decreases in \(\nu\), and \(\nu/\tanh(\nu h)\) increases. Their two endpoint evaluations enclose both coefficients throughout the physical cell.

The independent-amplitude test with four harmonics gives **\([137.7,138.9]\)** in 48 closed cells. The maximum verified upper endpoint is smaller than **0.997318768586407**. Together with the preceding intervals this establishes the conditional half-line \(L\ge137.7\).

~~~powershell
python -Bu complete_green.py --first 137.7 --last 138.9 --pieces 48 --uniform 2 --nh 8 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016' --free-green --tight-jump
~~~

Starting the four harmonic profiles at \(.775\) instead gives ten additional closed cells from \(137.5\) to \(137.7\) with upper endpoint **0.997530177490623**. The auxiliary moving lines remain valid, as every participating real part exceeds \(.75\).

~~~powershell
python -Bu complete_green.py --first 137.5 --last 137.7 --pieces 10 --uniform 2 --nh 9 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016,.020' --free-green --tight-jump --source-floor .775
~~~

The six-mode option uses \(1,2,4,6,8,12\) for the positive part and \(2,4,6,8,12,16\) for the absolute value. Every harmonic divides 96, so the angular sign changes are vertices of the same 192-cell certification grid. Six sources of oscillation cost at most a factor \(1+12\cdot10^{-6}\) on each moment boundary.

This six-harmonic choice gives **\([137.25,137.5]\)** in 25 closed cells. The largest complete upper endpoint is smaller than **0.998146248757153**.

~~~powershell
python -Bu complete_green.py --first 137.25 --last 137.5 --pieces 25 --uniform 2 --nh 6 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.008,.012,.016,.020' --free-green --tight-jump --source-floor .755 --more-modes
~~~

2026-11-20. Joint project attribution to Claude and Codex.
