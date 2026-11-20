# A free multiplier in the rational covariance estimate

Keep every geometric estimate and all three slabs from the [grouped stationary calculation](GROUPED.md). For \(Q=210,\alpha=1,w=.04,Z=384\), the upper bound for the complete normalized fourth moment of \(\zeta E_{210}\) on \(u=\log T\ge U\) now satisfies

| \(U\) | Fixed multiplier | Free multiplier |
|---:|---:|---:|
| 35 | .001147673 | .001140886 |
| 37 | .000997554 | .000989248 |
| 40 | .000850665 | .000842988 |

For a slab \([U,B]\) let \(s_r,v_r\) be the normalized variance upper bounds after removing the mean from \(S\) and the short nonstationary product from \(V\). For a signed trigonometric polynomial \(P\) use
\[
2 E[(S-m-P)(V-V_0)]\le\lambda E(S-m-P)^2+\lambda^{-1}E(V-V_0)^2
\quad(\lambda>0).
\]
The unprojected terms contribute \(\lambda s_r+v_r/\lambda\) in the normalized mixed upper bound. Write \(l_{rs}\) for the signed lower bound on \(E[(S-m)\cos(t\log(r/s))]\), and \(h'_{rs}\) for the absolute upper bound on \(E[(V-V_0)\cos(t\log(r/s))]\). The preceding proof gives both. Put \(\kappa=(B/U)^4/\lambda\). On a retained box let \(a_0>0\) minorize \(\sqrt{rs}(l_{rs}-\kappa h'_{rs})\). Use the coefficient \(a_0/(g\sqrt{rs})\) for each frequency in the box, where \(g\) is the doubled-frequency Hilbert upper bound. This subtracts at least
\[
 \frac{\lambda}{g B^4}\sum_{\rm boxes}a_0^2\,{\rm mass}({\rm box})
\]
from \(\lambda s_r+v_r/\lambda\). Indeed the individual signed variance reduction is nonnegative, so its denominator may be frozen at \(B^4\). Every compensating absolute upper uses \(U^4\). The remaining terms involving \(m,V_0\) and the AFE are the same for every choice of \(\lambda\).

The table uses nine positive multipliers between \(1\) and \(2.2\) times \(\sqrt{v_r/s_r}\). Choosing a member of this finite family separately on each slab gives a uniform upper bound there. The arithmetic of the boxes and their harmonic masses is shared. Lower signal endpoints, upper noise endpoints, and lower masses enter each individual calculation. The upper range \(u\ge U+1\) uses the preceding rational estimate there. The [verifier](dual_projection.py) evaluates the union of the four ranges.

~~~powershell
python -B round8/critical/dual_projection.py
~~~

2026-11-20. Joint project attribution to Claude and Codex.
