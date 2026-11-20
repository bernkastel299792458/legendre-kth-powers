# Explicit higher-degree zero-detecting polynomials

For $1.4\le\nu\le1.78$ this certificate gives a constant $c_\nu$ and a real polynomial $P$ with $P(0)=1$, $P'(0)=0$ and a zero of multiplicity at least $m$ at $-1$, such that $\log |P(z)|\le m c_\nu |z|^\nu$ for all $z\in\mathbb C$. The choices have $(\deg P,m)=(8,1)$ or $(15,3)$. At $\nu=1.55,1.65,1.72,1.75$ the certified constants are respectively below **.549609, .528612, .517545, .513011**. The verifier also covers intervals of exponents by selecting one complete polynomial for the interval.

The [exact rational coefficients](radial_detectors.py) were selected by exploratory linear programming. For a simple root the program chooses the quadratic coefficient by $P(-1)=0$. For a triple root it constructs $P=(1+z)^3 Q$, with the top coefficients taken from the table and $Q(0)=1,Q'(0)=-3$. The convolution and both low coefficients are checked using integers.

On a circle of radius $r$, write $a_j=[z^j]P$ and $h_k(r)=\sum_j a_ja_{j+k}r^{2j+k}$. The trigonometric polynomial

$$
F_r(t)=|P(re^{it})|^2=h_0(r)+2\sum_{k=1}^{\deg P} h_k(r)\cos(kt)
$$

is even. On $[0,\pi]$ evaluate it at 257 equally spaced points. Since $\|F_r''\|_\infty\le2\sum k^2|h_k|$, linear interpolation bounds its maximum by the largest sampled value plus $(\pi/256)^2\sum k^2|h_k|/4$. All operations use Arb. Evaluate at the 257 radii $r=2^{(j-128)/32}$, $0\le j\le256$. Hadamard's three-circles theorem says that $\log\max_t|P(re^{it})|$ is convex in $\log r$. If it is bounded at two successive radii by $C r^\nu$, applying the secant bound to the exponential in $\log r$ yields a uniform bound

$$
 C r^\nu\left(1+\tfrac18(\nu h)^2e^{\nu h}\right),\qquad h=\log(2)/32 .
$$

For the small-radius tail use $\log |P(z)|\le |P(z)-1|\le r^2\sum_{j\ge2}|a_j|(1/16)^{j-2}$. For $r\ge16$, write $A=\sum |a_j|16^j$. The majorant $(\log A+(\deg P)\log(r/16))/r^\nu$ decreases since $\nu\log A>\deg P$ for each polynomial. The checker divides the resulting bound by its actual guaranteed multiplicity $m$. At a fixed radius $r$ the ratio of any nonnegative logarithmic bound to $r^\nu$ is convex in $\nu$, so checking the enclosing endpoints on a mesh of width .005 covers the entire intervening exponent interval.

For use in the [Littlewood rectangle](../../round2/spectrum/PROOF.md), if $|w|\le1/4$, put $b=\sum_{j\ge2}|a_j|4^{2-j}$. The exact coefficient checks give $b/16<1/2$ and $b/(1-b/16)<2m$. Thus $\Re P(w)>1/2$ and $|\log P(w)|<2m|w|^2$. On the outer circle the coefficient checks give $|P(w)|\le(1+|w|)^{\deg P}$. Each zeta zero contributes at least $m$ times its multiplicity in the rectangle, including if the mollified zeta product vanishes to higher order. After division by $m$, both the right-edge bound and the two horizontal edge bounds are no larger than the old ones: the degree obeys $\deg P/m\le9$ and $m\ge1$. Real coefficients retain conjugate symmetry. This supplies a drop-in bound for the detector coefficient with all previously charged edge terms.

~~~sh
python -B round5/kernel/radial_detectors.py
~~~

2026-11-20. Project AI authors Claude and Codex. Codex selected the polynomials and derived the scalar certificate.
