# Short ordinate ranges needed by a first-band counterexample

Assume QRH(7/8) and the published inputs of the [lower endpoint proof](../../round3/low/FAREY.md). Set \(H=3\,000\,175\,332\,800\), the verified RH height. A fourth-power counterexample with \(115.032116<L=4\log n\le123\) would force at least **75,001** zeros with \(.72<\beta\le7/8\) and \(H<\gamma\le 27\,713\,503\,191\,610\). For \(L\le116\) in this range it would force at least **220,001** such zeros by height **4,650,273,045,841**. Only positive ordinates are counted, with multiplicity. These necessary conditions and the [previous rectangle](../../round3/low/FIRST_BOX.md) apply simultaneously. The new tests use a lower left edge in the real-part direction to reduce the height. They require no moment or density input above \(H\).

More precisely, each row individually suffices to force a prime in \((x,x+4x^{3/4})\) for *every* real \(x\) with \(L=\log x\) in its closed range, provided the number of indicated zeros in the corresponding rectangle does not exceed the allowance. The same is true with the weighted count (1).

| \(L\) range | Rounded upper ordinate | Allowed count |
|---|---:|---:|
| \([115.032114,116]\) | 4,650,273,045,841 | 220,000 |
| \([116,117]\) | 6,183,719,399,814 | 154,000 |
| \([117,118]\) | 7,940,052,515,472 | 123,000 |
| \([118,119]\) | 10,195,228,876,149 | 104,000 |
| \([119,120]\) | 13,090,932,642,370 | 92,000 |
| \([120,121]\) | 16,809,089,877,397 | 84,000 |
| \([121,122]\) | 21,583,298,270,414 | 79,000 |
| \([122,123]\) | 27,713,503,191,610 | 75,000 |

Take \(Q=10^4,\ b=.72\). For a row \([l,h]\) use \(K=1.55H\) in the first row and \(K=2.45/d(h)\) otherwise, where \(d(L)=\tfrac12\log(1+4e^{-L/4})\). Set \(T_1=K+128Q\) and \(S=K-H\). It suffices to bound
\[
 \sum_{\substack{H<\gamma\le T_1\\b<\beta\le7/8}}
     e^{-(7/8-\beta)l}\,
     \frac{(K-\gamma)_++Q/\sqrt\pi}{S+Q/\sqrt\pi}.                    \tag{1}
\]
Every individual weight is at most one. Rounding \(T_1\) upwards, as done in the table, only weakens the unweighted sufficient condition.

## Proof

Use the signed kernel, explicit formula, and scale-dependent sieve bounds in the [finite-height argument](../../round2/local/EDGE.md) with \(\eta=1.090,\ a=(1-10^{-12})Kd(h),\ I=\pi\sin(a)/a\). This choice keeps \(a<Kd(L)\) everywhere and \(0<a<\pi\). The sieve bound applies for arithmetic lengths \(y\ge e^{50}\). For \(y< e^{50}\) the tangent intercept exceeds \(e^{50}+1\) as in the [Farey proof](../../round3/low/FAREY.md): every tangent scale is at least \(1/512\) and at most 7, \(\log(se^c/K)+\eta<135\), and \(2e^l/(512 K\cdot135^2)>e^{50}+1\) in each row. The original arithmetic bounds, pole loss, archimedean term, and verified ordinates through \(H\) are thus available without modification. Denote their sum by \(B\).

Write \(X\) for a centered Gaussian of variance \(2Q^2\), and put \(m_1=S+Q/\sqrt\pi,\ m_2=S^2+2Q^2,\ m_3=S^3+6S^2Q/\sqrt\pi+6SQ^2+8Q^3/\sqrt\pi\). For \(H<\gamma\) the signed test has the bound
\[
 |G(\gamma-i(\beta-\tfrac12))|
 \le \frac{\pi e^{1/(16Q^2)}}{K^2}\,\mathbb E(K-\gamma+X)_+ .
\]
This follows from its exact nonnegative unsmoothed spectrum on \([-K,K]\) as in the finite-height argument. Pair a positive ordinate with its conjugate at negative height. Dividing the translated cosine bound by the pole normalization \(e^{c/2}I/K\) contributes the factor \(e^{-(1-\beta)c}+e^{-\beta c}\), besides \(K/I\). For \(1-b\le\beta\le b\), convexity and symmetry make this factor at most \(e^{-(1-b)l}+e^{-bl}\). The frozen-endpoint Riemann–von Mangoldt estimate of the earlier proof therefore bounds the **whole central strip** at heights above \(H\), in the chosen normalization, by
\[
 E_b=\frac{\pi e^{1/(16Q^2)}}{IK}(e^{-(1-b)l}+e^{-bl})
 \left[(.3\log H+6)m_1+
 \frac12\left(\frac{\log(H/(2\pi))}{2\pi}+\frac{.15}{H}\right)m_2
 +\frac{m_3}{12\pi H}\right].                                         \tag{2}
\]
This uses an upper bound on *all* ordinates when estimating the triangular sum in the central strip. It allows arbitrary multiplicities there. The count estimates hold for every \(S\ge0\), since they only use \(\log(1+v/H)\le v/H\).

For \(H<\gamma\le T_1,\ \beta>b\), pair each positive-ordinate zero on the right with its reflection \(1-\beta+i\gamma\), as well as its conjugate and the conjugate of the reflection. The functional equation preserves multiplicities. The right and left factors have the same modulus bound. For one such right zero
\[
 e^{-(1-\beta)c}+e^{-\beta c}
 \le e^{-l/8}e^{-(7/8-\beta)l}\bigl(1+e^{-(2b-1)l}\bigr).
\]
Moreover \(\mathbb E(K-\gamma+X)_+\le (K-\gamma)_++Q/\sqrt\pi\). The total charge from the two outer strips through \(T_1\) is thus bounded by (1) times
\[
 P=\frac{2\pi e^{1/(16Q^2)}}{IK}\,
     e^{-l/8}(1+e^{-(2b-1)l})(S+Q/\sqrt\pi).                         \tag{3}
\]
The factor of two here counts the real-part reflections. Negative ordinates were already included in the exponential pair.

Above \(T_1\) the [Gaussian-tail proof](../../lower/PROOF.md) applied at its lower endpoint \(T_1>K\) covers *all* real parts even without QRH. With \(g_0=(1-\cos a)/a^2\) it contributes at most
\[
 E_\infty=\frac{2K}{I}\frac{2\pi g_0}{2\sqrt\pi Q}
 e^{1/(16Q^2)}T_1^2(1+4/128^2)e^{-128^2/4}<10^{-1700}.
\]
Double-counting the central strip in this tail is harmless. In each row the [192-bit verifier](near_height.py) checks \(B+E_b+P\cdot\mathrm{allowance}+E_\infty<1\), which contradicts the empty-interval hypothesis in the explicit formula. It computes \(B\) by subtracting the original all-QRH high-zero term from the same ball-valued total; interval subtraction preserves the enclosure even for dependent operands. The resulting *unrounded* count allowances exceed \(221236.89,\ 154738.78,\ 123596.77,\ 104808.15,\ 92680.28,\ 84693.46,\ 79439.88,\ 75920.62\) respectively.

No existing upper count in these rectangles is assumed or verified here. The numerical verification uses Python with python-flint and the pre-existing explicit-formula certificate. The written mathematics has no separate Lean verification. Project attribution to Claude and Codex. Codex derived the compact-height transfer.
