# The 30 count conditions under reflection, ordinate moments and cumulative distance bounds

Each of the [30 finite conditions](GRID_TARGET.md) can fail on a symmetric point configuration while the other 29 hold. Each witness satisfies the finite-height critical-line condition, the $7/8$ strip, the explicit cumulative distance bounds detailed below and the upper Poisson sampling estimate used by the [Gaussian detector](../left/large_values/GAUSSIAN.md). It can have precisely the same list of ordinates, including multiplicities, as a comparison configuration meeting all 30 conditions. This gives a limitation of these inequalities as inputs. The witnesses are discrete models, and do not satisfy a claimed Euler product or explicit formula for the Riemann zeta function.

Let $(s,T)$ be the chosen condition and let $B=6(\log T)T^{3(1-s)/(3s-1)}$. Choose $m=\lfloor1.2B\rfloor$ pairs with real parts $\beta=s+10^{-8}$ and $1-\beta$ at distinct positive ordinates in $(Te^{-.05},T]$. Include the conjugate pair at each negative ordinate. The script verifies $m>B$ in every case. Every earlier marked height lies below this short band. A different condition with threshold at least $\beta$ counts none of these points. Every remaining right-hand side, at the same or a later height and a lower real threshold, exceeds $1.2B$. All counts in this note use multiplicities.

## A configuration on the Riemann–von Mangoldt scale

Write $F(t)=t(\log(t/(2\pi))-1)/(2\pi)$. Above $t=200$ place simple zeros on the critical line at $F(t)\in\mathbb Z$; any actual initial zeros below that cutoff may be retained. At the $j$-th of the desired pairs take the first grid ordinate $\gamma_j\ge Te^{-.05}+2000j$, $0\le j<m$. These ordinates differ by at least 1999 since $F'(t)>4$ in the active range. Each such ordinate and its successor lie below $T$, as the script verifies with spare length. Move the successor onto $\gamma_j$, then replace these two critical-line zeros by one reflected pair. The comparison configuration leaves the pair on the line. If distinct zeros are desired in both configurations, the comparison pair may instead have real parts $1/2\pm10^{-12}$ with identical ordinates.

Both lists then have the same sums of **every function of the ordinates alone** whenever the sum is defined. For $H\le v\le t$, their common total-zero count satisfies

$$
|N(t)-N(v)-F(t)+F(v)|\le2 .
$$

Indeed before the merges $N(t)-F(t)$ varies within an interval of width one, and each merge changes a prefix count by either 0 or 1. Only one such change can be active at a time. Both configurations have all their low zeros on the line and satisfy the local total-count majorants used in the certificate. The prescribed exact ordinates below the verification height are not inputs to this model.

## Real-part inequalities

For $r\ge 1/2$, the cumulative distance above $H$ of the witness is at most $m(\beta-r)_+$; the reflected left partner contributes zero. Before $Te^{-.05}$ it vanishes identically. The lower-height modulus-210 rectangle supplies bounds of the form

$$
\Lambda_r(t)\le B_r t^{p_r}(\log t)^{1+p_r}+E_c+E_s\log t,\qquad
p_r=\frac{3(1-r)}{2-r}.
$$

Using $U=28.7$ and the [explicit coefficient](../low/short_box.py), these hold simultaneously for the 225 grid values $r=.650,.651,\ldots,.874$ and $t\ge H$. Their right sides increase in $t$. At $t=Te^{-.05}$ even the smallest right-hand side divided by $(\beta-r)B$, over all positive denominators, all 225 abscissae and all 30 witnesses, exceeds **25.49**. The tested conditions therefore hold for all heights. The final strip bounds used in the 30-rectangle proof, reanchored at $T_*=He^{51/4}$ with the short core of length 32768, are also tested at $T_*$ with their own real grid and are increasing thereafter. Convex interpolation of genuine cumulative hinge values, or integration of these pointwise bounds against a positive height measure, preserves feasibility.

There is also an optional, stronger check. At each of the six marked heights it uses all five pairs of global norm bounds from the [fixed-height study](../low/FINITE_POINTS.md), with core length $2^{17}$. For each such pair and every auxiliary $r<\beta$ the radial Jensen floor there, with $\sigma=\beta$, lower-bounds its bound on $\Lambda_r/(\beta-r)$. Norm and edge losses have been dropped in this floor. Taking the minimum over all these pairs, all current or later marked heights, and all witnesses still permits more than $7.45B$. This last assertion concerns the five registered norm choices at their marked heights.

## The Poisson upper estimate even sees both reflected real parts

Let $P_a(x)=a/(a^2+x^2)$. For every $H-40\le t\le e^{45}+40$ and $1.1\le c\le1.25$ the full witness obeys

$$
\sum_\rho P_{c-\Re\rho}(t-\Im\rho)
\le\frac12\log\frac{|c-1/2+it|}{2\pi}+2.64 .
$$

The positive Dirichlet series $-\zeta'(c)/\zeta(c)$ exceeds 2.87 throughout this $c$-range: it suffices to keep the prime powers of primes through 2003 at $c=1.25$. Consequently the witness satisfies the upper envelope $F_s(\log Z)$ in the Gaussian detector whenever $t\le Z+40$, $Z\ge H$ and $c=2s-1/2$. This verifies an inequality; the model does not impose the pointwise equality to a zeta logarithmic derivative.

Here are details of the uniform constants. Start with the critical-line quantile grid and put $a=c-1/2$. Choose $b_0\in[H/2,H/2+1]$ so that $F(b_0)$ is a half-integer. The total contribution at high $t$ from the two signs of the ordinates below $b_0$ is less than $10^{-8}$ (use $N(b_0)\le b_0\log b_0$ and distance $>H/3$). Above $b_0$ do midpoint quadrature in $F(w)$, on each signed half-axis. On a unit cell the Peano kernel for the midpoint has absolute supremum $1/8$. With $g=F'>4$ at positive arguments $w\ge b_0$, substitution gives the combined absolute error bound

$$
\frac18\left(\frac14\int_{\mathbb R}|P_a''(x)|\,dx
       +\sup_{w\ge b_0}\frac{|g'(w)|}{g(w)^2}
                \int_{\mathbb R}|P_a'(x)|\,dx\right).
$$

Both signed half-axes use disjoint subintervals of the integrals over $\mathbb R$. One has $\int|P_a''|=3\sqrt3/(2a^2)$ and $\int|P_a'|=2/a$; the second term in parentheses is below $10^{-11}$. Completing the continuous integral to the whole line costs less than $10^{-20}$ for the negative density on $|w|<2\pi$. The result follows from the Poisson extension of $\log|w|$,

$$
\int_{\mathbb R}P_a(t-w)\frac{\log(|w|/(2\pi))}{2\pi}\,dw
=\frac12\log\frac{|a+it|}{2\pi}.
$$

The spare allowance $10^{-8}$ in the script covers the low ordinates and this completion together. A selected successor moves by at most $1/4$. The nearest moved ordinate can increase the sum by at most $\frac14\|P_a'\|_\infty=9/(32\sqrt3 a^2)$. The other signed selected ordinates have distances at least $(j-1/2)1999$ in each direction. Their combined change is below $10^{-8}$ by $|P_a'(x)|\le2a/|x|^3$, allowing another $1/4$ in the distance.

Finally let $d=\beta-1/2$. For the closest horizontally split pair, Fourier inversion of $P_a$ bounds the increase by

$$
\int_0^\infty 2e^{-av}(\cosh(dv)-1)\,dv
=\frac{2d^2}{a(a^2-d^2)} .
$$

For all other pairs the absolute change at distance $x$ is bounded by $4a/x^2\le3/x^2$. Both tails together add at most $3\pi^2/1999^2$. The script adds these costs at $a=.6$, $d=.36500001$ for the nearest-pair terms. It verifies the total is strictly below 2.64.

The full range of the [two-reflected-root sampler](../spectrum/REFLECTION.md), $1.08\le c\le1.36$, also passes. Divide it into closed intervals of length .01. On each interval use its left endpoint in the decreasing nearest and quadrature costs, its right endpoint for $-\zeta'(c)/\zeta(c)$, and $4a\le3.44$ for the distant split pairs. The absolute allowances $10^{-8}$ and $10^{-11}$ still cover the low ordinates, distant vertical displacements and density-derivative error at $.58\le a\le.86$. The difference between the available finite prime-power sum and the model's Poisson excess exceeds **1.21406** on the entire range.

~~~sh
python -B round5/kernel/rectangle_models.py
python -B round5/kernel/rectangle_models.py --fixed
~~~

2026-11-20. Project AI authors: Claude and Codex. Codex derived and checked this finite model.
