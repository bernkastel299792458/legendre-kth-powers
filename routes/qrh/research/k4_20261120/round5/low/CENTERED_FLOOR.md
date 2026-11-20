# The diagonal cost in one proposed centered density bound

The first three [short-box implications](SHORT_BOX.md) use \(T=3000175332800\) and request bounds of \(75000,\ 230000,\ 19000\) at \(\sigma=.80,.81,.82\) and window lengths \(\Delta=.008T+1280000,.05T+1280000,.05T+1280000\), respectively. A parameter-independent lower estimate on the right side of [rStation 168, theorem 1, v1](https://rstation.ai/problems/riemann_hypothesis/papers/168) shows how much of the cost is already present before the dual sum and the horizontal edges enter. This calculation is about the displayed formula and uses no result from the manuscript as a mathematical input.

Take any of the permitted \(\sigma',X,x\). Define \(q=\sigma-\sigma'>0,\ b=2\sigma-1,\ a=2\sigma'-1=b-2q\). The theorem's diagonal cost is
\[
 A_\Delta=(D-1)(1+2\pi m_0(x+1)/\Delta),\qquad D=(1-X^{-a}/(a\zeta(1+a)))^{-1}.
\]
The decreasing-integral bound gives \(a\zeta(1+a)\le1+a<1+b\). Therefore \(D-1\geq X^{-a}/(1+b)\). Since \(X\leq x\) and \(2\pi m_0>6\), set \(y=6X/\Delta\). The inequality \(1+y\geq y^a\), for \(0<a<1\), yields \(A_\Delta\geq z=(6/\Delta)^a/(1+b)\). The displayed \(V_\Delta\) is at least \(A_\Delta\), and \(0< z<1\) gives \(\log(1+V_\Delta)\geq z/2\). The nonnegative rectangle cost can likewise be dropped when bounding the expression from below. The function \(e^{2q\log(\Delta/6)}/q\) has global minimum \(2e\log(\Delta/6)\) for \(q>0\). Combining these yields the floor
\[
 \frac{\Delta\log(1+V_\Delta)/(2\pi)+\mathcal{E}_\Delta}{\sigma-\sigma'}
 \ \geq\
 \frac{\Delta}{2\pi(1+b)}(6/\Delta)^b e\log(\Delta/6).
\]

[192-bit Arb arithmetic](centered_floor.py) makes the three floors respectively greater than \(248640,342880,209823\). Each exceeds the corresponding [required budget](SHORT_BOX.md). This proves a limitation for direct use of this particular bound at those three widths. Local estimates which change the diagonal control or exploit soft weighting may have different costs.
