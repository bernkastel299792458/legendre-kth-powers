# Raw Green tests with several independently priced sources

Under the assumptions of [RAW_GREEN.md](RAW_GREEN.md), fix real knots \(a_0<\cdots<a_k\), an allowed angular frequency \(\nu\), and prescribed values \(v_0=0,v_1,\ldots,v_k\ge0\). Set \(V=0\) on the left of \(a_0\). On \([a_i,a_{i+1}]\) solve \(V''=\nu^2 V\) with endpoint values \(v_i,v_{i+1}\). To the right of \(a_k\) put \(V=v_ke^{-\nu(\sigma-a_k)}\). These pieces have nonnegative values. Write \(h_i=a_{i+1}-a_i\). The right derivative at \(a_i\) and left derivative at \(a_{i+1}\) on an internal cell are, respectively,

\[
 \nu\frac{v_{i+1}-v_i\cosh(\nu h_i)}{\sinh(\nu h_i)},\qquad
 \nu\frac{v_{i+1}\cosh(\nu h_i)-v_i}{\sinh(\nu h_i)}.
\]

The two outside derivatives are zero and \(-\nu v_k\). Denote the derivative jump at \(a_i\) by \(d_i\). Starting with \(B=B'=0\) on the left, choose a nonnegative constant \(b_i\) at least \(|d_i|\), and at an internal knot also at least \((v_{i+1}-B(a_i))/h_i-B'(a_i-)\). The implementation rounds this maximum upwards across the entire frequency interval. Use \(B(\sigma)=\sum b_i(\sigma-a_i)_+\). By induction \(B(a_i)\ge v_i\) at every knot. Each intermediate \(V\) is convex, so \(B\ge V\) there as well. On the two exterior intervals the same statement follows from zero extension on the left and decay on the right.

Consequently \(\Psi=B+V\cos(\nu t)\) is nonnegative on every determinant zero, including unwanted zeros to the right of the QRH strip. Its exact source on \(a_i\) has coefficient \(b_i+d_i\cos(\nu t)\), also nonnegative. On a horizontal edge \(|\Psi_\sigma|\le\sum b_i+\sup |V'|\). On the right, \(|\nabla\Psi|\le\sum b_i+\max(\sup |V'|,\nu\sup V)\). Since \(V''\ge0\) in each cell, the supremum of \(|V'|\) is at a one-sided endpoint and \(\sup V\le\max_i v_i\). These give the complete edge constant. The source integral at a knot costs at most \(b_i\) times the unit-amplitude weighted moment already used for the two-source tests. Each whole test uses one fixed determinant and taper, with separately selectable auxiliary interpolation lines on its sources.

In the positive spatial band, a positive combination of these raw tests majorizes the positive cosine portion whenever the combined profile \(B+\alpha V\) dominates the physical hinge profile at every real-part vertex, with \(\alpha=\nu g/\sinh(\nu g)\) on the finest test grid of maximal step \(g\). The [two-source proof](RAW_GREEN.md) applies without change to every interval between these vertices. A floating linear program proposes coefficients only. The [raw multi-source verifier](multi_raw.py) recomputes the coverage of every selected column at every vertex in Arb, rescales all coefficients upwards if needed, and independently minimizes each complete determinant cost on the archived rows. A feasible angular plan is independent of height. It can be reused on other height samples by reevaluating all selected costs there. The program also charges scalar hinges and the original finite/infinite residuals.

The template menu contains 2, 3, 4, 6 and 9 source knots on an equally spaced subgrid. Sampled nodal amplitudes have linear or exponentially increasing increments; the terminal amplitude can be reduced. This menu proposes arbitrary legal nonnegative amplitudes and is not an assumption about zeta. On \([140.5,140.51]\) the ordinary scalar cost exceeds \(1.0813260\). Combining the many-source raw estimate in the positive band with the absolute two-frequency estimate at later heights gives a complete upper bound below \(0.961165\).

~~~powershell
python -Bu complete_green.py --first 140.5 --last 140.51 --nh 4 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016' --multi-raw --raw-abs --reuse-raw 4
~~~

When the frozen source table starts at \(T_0=e^{33}\) beyond the end of the spatial envelope's initial flat part, the program sets the first Abel level to one. The first charged cumulative population runs through the next sampled height \(T_1>T_0\), and thus includes every verified-height successor before \(T_0\). This covers all missing lower ordinates. For physical cells extending below 140 the uniform Poisson attenuation cutoff is 135. All actual frequencies are checked to be at least that value.

The full closed bridge \([139.55,140.65]\) consists of 44 physical cells of length .025. Its maximum rigorously rounded upper endpoint is below **0.994242879019920**. At the first cell the ordinary scalar cost exceeds 1.11396. This bridges directly to the closed upper half-line at 140.65 proved in [RAW_GREEN.md](RAW_GREEN.md), giving conditional coverage of every \(L\ge139.55\). A separate cell \([139.4,139.41]\) has complete cost below 0.994151.

~~~powershell
python -Bu complete_green.py --first 139.55 --last 140.65 --pieces 44 --uniform 6 --nh 6 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016' --multi-raw --raw-abs --reuse-raw 4
~~~

Fifteen further closed cells give \([139.25,139.55]\) with maximum upper endpoint below **0.999904036247959**. The ordinary bound on the first cell is above 1.12323. Together the connected bridges establish the conditional half-line \(L\ge139.25\).

~~~powershell
python -Bu complete_green.py --first 139.25 --last 139.55 --pieces 15 --uniform 3 --nh 8 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016' --multi-raw --raw-abs --reuse-raw 4
~~~

2026-11-20. Joint project attribution to Claude and Codex.
