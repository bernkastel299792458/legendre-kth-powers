# Sieve level required by the positive exterior at larger locations

The positive-main-term version of the current bandlimited sieve requires a different scale by \(L=116\). This comparison specifically applies when the near positive exterior is charged with majorants of the form \(y/G(z)\) plus nonnegative errors, using \(z\le C\sqrt{e^L/K}\). It allows varying the sieve level across the lobes or individual heights under that ceiling. A signed remainder or a new test is outside this diagnostic.

At a fixed location write \(c=L+d,\ d=\log(1+4e^{-L/4})/2,\ a=(1-10^{-12})Kd,\ I=\pi\sin(a)/a,\ r=10^{-6}\) and \(Q=10000\). For the old kernel the exterior positive area in angular units divided by \(I\) is exactly \(1-a/\pi\). Passing from the test boundary \(a\) to the actual target boundary \(Kd\) discards at most \(2(Kd-a)g(0)/I\), since the nonnegative transform gives \(|g(u)|\le g(0)\). Removing the part beyond \(|u|>Kr\) costs at most \(4/[IKr(1-(a/(Kr))^2)]\). Within the remaining region \((c+v)e^{v/2-(Qv)^2}\ge(c-r)e^{-r/2-(Qr)^2}\). The Selberg main term on that positive portion alone, in the same explicit-formula normalization, is therefore at least
\[
 \frac{(c-r)e^{-r/2-(Qr)^2}}{G(C\sqrt{e^L/K})}
 \left(1-\frac a\pi-\frac{2(Kd-a)g(0)}I-
       \frac4{IKr(1-(a/(Kr))^2)}\right).
\]
This is a lower bound on the *cost of that analytical upper-bound method*. It uses the monotonicity of the positive sum \(G(z)\). With the [Ramaré upper estimate](BILINEAR.md) \(G(z)\le\log z+2+2.44/\sqrt z\), interval arithmetic proves this cost already exceeds one at the following dimensionless sieve-level ceilings.

| \(L\) | Ceiling \(C\), \(K=H\) | Ceiling \(C\), \(K=H+16000000000\) |
|---:|---:|---:|
| 115.4 | 130 | 90 |
| 115.5 | 660 | 470 |
| 116 | 1160000 | 860000 |
| 117 | 340000000000 | 265000000000 |

For example, when \(L=116,\ K=H,\ C=1160000\), the lower charge exceeds \(1.0006417\) before adding any zero or oscillatory error. In the top Selberg blocks \(g=1,\ i=j=0\) the \(n=1\) reference phase scale at \(t=e^L\) is \(t/z^2=K/C^2<2.23\). At \(L=117\) the corresponding scale is below \(2.60\,10^{-11}\). Thus increasing the sieve level to the values required by the main term simultaneously removes strong oscillation from the basic top block. The finite upper bounds available on individual prime gaps are consistent with this limitation.

~~~powershell
python -B round7/physical/main_obstruction.py
~~~
