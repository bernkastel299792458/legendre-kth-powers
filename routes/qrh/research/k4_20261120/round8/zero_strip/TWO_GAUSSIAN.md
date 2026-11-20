# A two-band positive detector and its arithmetic threshold

One positive alternative to the triangular strip detector has boundary function \(F(y)=e^{-v^2y^2/2}(1+\cos Uy)\). Its extension to the strip is positive by the same harmonic argument as the [triangular case](STRIP_BOUNDARY.md). In the cosine-transform convention of that note, its nonnegative boundary spectrum is
\[
 q(u)=\frac2M e^{-u^2/(2v^2)}
       +\frac1M\left[e^{-(u-U)^2/(2v^2)}+e^{-(u+U)^2/(2v^2)}\right],
 \quad u\ge0,\qquad M=\sqrt{2\pi}v .
\]
It splits the arithmetic into a low Gaussian and the high Gaussian already used in the [signed calculation](PACKET.md). The associated gamma main term on the previous half-normalization is \(q(0)\log(t/(2\pi))/4\). No triangular or independent-shell obstruction was used for this detector.

At the representative \(U=35.5,\ v=6,\ \beta=s=.865\), the full positive single-root area times 420070 is at most **9466.911** for the common endpoint \(B=q(0)\log(T/(2\pi))/4\), before charging small primes or any analytic correction. This is a favorable cost benchmark for a uniform single-root method that uses these two moments. The present modulus-210 length-norm upper-bound expression for the high band already charges **14836.6476**, even granting a factor of two for its real part, omitting positive padding and edge costs, and granting the low band free of charge. The ratio exceeds **1.56721**. This diagnoses the particular upper-bound expression at one parameter point. It makes no claim about the size of the true prime sum or about all two-band choices.

Here is an upper bound on the single-root area used in the comparison. Write \(a=\Theta-s=.01,\ b=\Theta-1/2=.375,\ k=e^{-aU+a^2v^2/2}\). The strip ratio \(\cosh((b-a)u)/\cosh(bu)\) differs from \(e^{-au}\) by at most \(2au e^{-(2b-a)u}\). Since \(q\le4/M\), the uniform error on the response \(G_s(y)\) is at most \(8a/[M(2b-a)^2]\). In the high part let \(Z\) have mean \(U\) and variance \(v^2\), and replace \(e^{-a|Z|}\) by \(e^{-aZ}\). The negative Gaussian tail costs at most \(k\,\operatorname{erfc}((U-av^2)/(\sqrt2v))\). Its remaining full transform equals \(k e^{-v^2y^2/2}\cos((U-av^2)y)\). Denote the sum of these two small errors by \(E\).

For the low Gaussian use
\[
 e^{-a|Z|}=1-a|Z|+O(a^2 Z^2/2)
\]
with absolute constant one. For a centered Gaussian of variance \(v^2\),
\(\mathbb E[|Z|\cos(yZ)]=v\sqrt{2/\pi}(1-2x\,\mathcal D(x))\), \(x=v|y|/\sqrt2,\ \mathcal D(x)=\tfrac{\sqrt\pi}2 e^{-x^2}\operatorname{erfi}(x)\). This follows by integrating the half-line first-moment Gaussian transform by parts. Combining these bounds gives
\[
 G_s(y)\le e^{-v^2y^2/2}[1+k\cos((U-av^2)y)]
          -av\sqrt{2/\pi}[1-2x\mathcal D(x)]+a^2v^2/2+E .
\]
The simpler low-Gaussian error \(av\sqrt{2/\pi}\) shows \([G_s(y)-B]_+=0\) for \(|y|\ge.4\). The verifier covers the remaining symmetric interval by 1024 upper rectangles on its positive half, using that \(\operatorname{erfi}\) increases there. It compares with \(\min(T S_0+.915503 S_1,(T-H)S_0+2(.915503)S_1)/(2M^2)\), using the [same arithmetic diagonal upper envelopes](POWER_PACKET.md).

~~~powershell
python -B two_gaussian_gate.py
~~~

2026-11-20. Joint project attribution to Claude and Codex.
