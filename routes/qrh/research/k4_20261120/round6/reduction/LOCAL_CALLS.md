# True hinge bounds on windows starting above the verified height

Take $l=H\exp(j/b)$ and $t=H\exp(k/b)$ with $0\le j<k$. Put $R=(t-l)/2$, $C=(t+l)/2$, $v=1.01$, $B=C+vR$, $M=2048$, and $U=\log R$. The [verifier](local_calls.py) returns upper bounds on $\sum_{l<\gamma\le t}(\beta-s)_+$, counted with positive ordinates and multiplicity.

Use the [translated rational window](../../round5/low/MOVING_WINDOW.md) centered at this $C$ with radius $R$. Its proof only uses $C\ge R$, the checked window-normalization inequalities, and lower height $l\ge H$. The full-axis interpolation contributes a factor two. Bound the half-integral of the critical factor by the global [centered fourth moment](../phase/CENTERED_PHASE.md) on the positive half-line up to $C+u$ in each layer $u\ge vR$. If $p=1+4/\log B$ and $c_4$ is the centered coefficient valid from $B$ onwards, this gives
$$
 A_4=\tfrac12 c_4 B\log^4 B\,\frac{M}{M-p}\{1+(vR/C)^{M-p}\}.
$$
Conjugating the polynomial coefficients by $n^{-iC}$ leaves the [folded critical mean](../folds/FOLD_MEAN.md) and right variance valid. The full function on the two sides is $f_{2310}$. The critical factor is $\zeta E_{210}$, the residual polynomial is $E_{11}C_{2310}$, and the folding depth is 12. Use the same triple $(\delta,W,\log h)$ on every side. The right mean uses the [matched $Q=2310$ estimates](../folds/MODULUS_2310.md) at scale $R$ and $100R$ cutoff. The angular Jensen bound on the two horizontal edges uses actual upper height $t$, the lower-height modulus estimates with $H-2$, and all five Euler primes. The right vertical edge has physical length $2R$. With the half-axis left and right norms $A_L,A_R$, the integral coefficient is $c_\nu\mathcal N^\nu A_L^p A_R^{1-p}/\pi$, where this $p$ now denotes the interpolation exponent of the [pointwise bridge](EXACT_BRIDGE.md). Pass to the lower horizontal edge from above to exclude $l$ and the upper horizontal edge from above to include $t$, with the detector coefficients fixed.

The optional [short-polynomial improvement](translated_short.py) uses the [previous translated short mean](../first_rect/PROOF.md) at arbitrary midpoint $C$. In that argument, before taking any cumulative outer integral, the near window is $[C-J,C+J]$, where $J=1.02vR$. Its two Riemann–Siegel cutoffs, error, and derivative denominators therefore use the actual $C-J,C+J$, as does the signed first-moment error. The outer layers use the same positive half-line second moment with $B=C+vR$. The code checks $C-J>200$. In the residual critical-line mean, every short core used in the subtraction satisfies $11n<210v(1.03)R/(12\pi)$. The harmonic saving on this low-frequency segment is multiplied by $1+1/11$, the squared divisor factor of $E_{11}$. This is the short-core calculation in the complete $f_{2310}$ normalization. All other constants and both terms of the signed first-moment minimum are unchanged from the translated-short proof.

At $j=28,b=16$ the unsplit bounds on the first subwindow $k=29$, at $s=.825,.850,.865$, are below $462894,83808,29443$. They are, respectively, less than $.651,.767,.844$ times the complete uncentered upper hinges at the same terminal height produced by the five-parameter strong-row menu. At log width $1/8$ the three ratios are less than $.776,.886,.958$. These are local hinge bounds, which alone do not establish a missing full count rectangle.

The short-core calculation on that first interval improves the three bounds to $448004,81524,28773$. Dividing at each lower real node $v$ by $s-v$ gives genuine local counts. For $.865<\beta\le7/8$, $H e^{7/4}<\gamma\le H e^{7/4+1/16}$ the number is at most **5,429,699**. Extending the upper log height by $1/8$ in place of $1/16$ yields **6,468,402**. These use the upper ends $5429699.156010$ and $6468402.177036$ before taking the integer floor.

The optional `--increments` argument of the [coupled verifier](coupled.py) includes these translated bounds immediately after each selected count-height and after $H$, up to one, two and four ordinary height steps. At a node $v$ each row adds $\sum_j(R_{b,j}-R_{a,j})(s_j-v)_+\le A_v(a,b)$ with $R$ the cumulative real-part masses. A nonnegative proposed coefficient adds to the dual hinge row at $b$ and subtracts at $a$. When the dual is accumulated backwards the coefficient is therefore present precisely on increments in $(a,b]$. As in the [full certificate](COUPLED.md), every missing scalar payoff is covered by a nonnegative atom-count correction. The six-rectangle global budget uses the earlier complete cumulative rows without this optional input.

For the five candidate pairs $(5,860),(8,845),(12,828),(18,862),(30,853)$, the extra windows reduce the full normalized upper budget on the $1/32$-wide cell starting at $116.5$ from $1.07982\pm.000005$ to $1.07096\pm.000004$. At $123$ the corresponding bounds are $1.09934\pm.000005$ and $1.09924\pm.000005$. These additional rows improve strict local count estimates and leave this five-rectangle proposal unresolved.

~~~sh
python -B round6/reduction/local_calls.py --start 28
python -B round6/reduction/local_calls.py --start 28 --short --counts
python -B round6/reduction/five_search.py --compare-increments
~~~

2026-11-20. Joint project attribution to Claude and Codex. Codex derived and checked the translated high-ordinate application and its finite certificates.
