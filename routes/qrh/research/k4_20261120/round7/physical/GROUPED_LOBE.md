# Grouped frequencies for the directly integrated lobe sieve

The [integrated-lobe certificate](WEIGHTED_LOBE.md) admits a small additional improvement from the simultaneous Fourier sampling bound in [GROUPS.md](extras/GROUPS.md). The stronger coefficient-discrepancy alternative in the latter paper is unnecessary here. The extra frequency groups exploit collisions \(n/w=n'/w'\) with nonnegative harmonic weights.

For a group \(N\le n\le J\), write \(H_1=J-N,\ h_p=\sum_{N\le n\le J} n^{-p}\). With \(p=0,1,2\), normalized group weights are \(\alpha_n=n^{-p}/h_p\). The two moments needed here are
\[
 v_0(p)=h_{2p}/h_p^2,\qquad v_\tau(p)=
        \frac{H_1}{h_p^2}\sum_{n=N}^J n^{-2p-1}\tau(n).
\]
For one sampling orientation the normalized bilinear modulus is at most
\(\sqrt{U_x P_{B_0}(U_w v_0+L_w^2 v_\tau)}\), using the notation of the cited group proof. The frequencies may carry arbitrary complex multipliers of modulus one, since their moduli remain unchanged in the collision Cauchy–Schwarz step. Thus the estimate may also be used for an absolute group sum or uniformly inside the height integrals. The transposed and separately bounded-frequency estimates remain available.

For the direct sawtooth charges, the undifferentiated sum uses \(p=1\). In a high-frequency integration by parts \(p=2\) and the scale multiplier contains \(h_2/h_1\); in the low-frequency signed difference \(p=0\) on the reciprocal-multiplied rows and the scale is \(h_0/h_1\). For each block take the lesser of the undifferentiated and high-frequency options separately for the moving and internal endpoints and average these two results. For secondary lobes use just their moving estimate. Compare the result with the signed low-frequency option. The geometric source integral factors and the entire infinite tail are those from the lobe proof.

For \(J\le4096\) calculate \(\tau(n)\) and all the required moments directly. For larger groups put \(d=J-N+1\). A divisor and its paired co-divisor show \(\sum_{n=N}^J\tau(n)\le 2\{d(1+\tfrac12\log J)+\sqrt J\}\), by counting divisors up to \(\sqrt J\). Since \(h_p\ge d J^{-p}\), it follows that
\[
 v_0(p)\le (J/N)^{2p}/d,\qquad
 v_\tau(p)\le \frac{(J/N)^{2p}(J-N)}{d^2 N}
                    2\{d(1+\tfrac12\log J)+\sqrt J\}.
\]
Use \(h_2\le N^{-2}+N^{-1}-J^{-1}\) or \(d/N^2\), by the decreasing integral comparison. The harmonic coefficient \(h_1\) is computed as \(\psi(J+1)-\psi(N)\) in Arb. For the Poisson tail the same frequency cutoff \(2^{48}\), 44 blocks and \(g,h\le2^{40}\) apply. The script uses the single-frequency weight norm estimates unchanged and at most 4,444,110 positive terms per group. The additional frequency-moment factors and sample bandwidths are positive and stay well inside the normal binary64 range; the aggregate retains its \(1+10^{-7}\) guard.

The [program](grouped_lobes.py) evaluates the earlier physical geometry with an isolated function namespace substituting only the right-hand side of this Fourier bound. The following closed slabs have complete costs below the numbers shown. The first reaches \(115.292\) without restricting zeros above the verified height. The latter two continue the QRH(7/8) endpoint through \(115.298\).

| Closed \(\log x\) slab | Hypothesis | Upper cost |
|---|---|---:|
| \([115.285,115.292]\) | finite RH verification | .999954 |
| \([115.290,115.297]\) | QRH(7/8) | .999547 |
| \([115.296,115.298]\) | QRH(7/8) | .999846 |

~~~powershell
python -B round7/physical/grouped_lobes.py --lo 115.285 --hi 115.292 --ratio 73 --secondary-ratio 81 --check
python -B round7/physical/grouped_lobes.py --lo 115.29 --hi 115.297 --ratio 74 --secondary-ratio 81 --qrh --check
python -B round7/physical/grouped_lobes.py --lo 115.296 --hi 115.298 --ratio 72 --secondary-ratio 81 --qrh --check
~~~
