# A length-dependent sieve obstruction for bandlimited tests

The local upper bound \(2y/(\log y+1.090)\) admits a periodic angular density which vanishes on the target interval and gives the correct mean for *every* integrable real bandlimited test at the verified height. The statement about all tests is exact in the angular coordinate. In the arithmetic coordinate we give the sieve inequality on every interval and quantify the localization and rounding errors in the test identity. The construction describes a limitation on these particular inputs. Its artificial measure does not satisfy any asserted zeta explicit formula.

Write \(L=\log x,\ d=\tfrac12\log(1+4e^{-L/4}),\ c=L+d,\ H=3\,000\,175\,332\,800,\ b=Hd,\ u=H(\log t-c)\). The open target has \(|u|<b\). For \(0<b<\pi\), put \(s=2\pi-2b,\ A=2\pi/s\) and
\[
 P_b(u)=A\,\mathbf1_{\operatorname{dist}(u,2\pi\mathbb Z)>b}.
\]
For every \(g\in L^1(\mathbb R)\) whose angular Fourier transform is supported on \([-1,1]\),
\[
 \int_{\mathbb R}g(u)P_b(u)\,du=\int_{\mathbb R}g(u)\,du. \tag{1}
\]
Indeed the \(L^1\) periodization of \(g\) has all nonconstant Fourier coefficients zero. Continuity of the Fourier transform makes its values at the two band endpoints zero as well. Fourier uniqueness on the circle makes the periodization constant almost everywhere. The bounded multiplier \(P_b\) has mean one.

For each \(w=2\pi k+v>0\), \(k=\lfloor w/(2\pi)\rfloor,\ 0\le v<2\pi\), the **exact** maximum of \(\int_J P_b\) over all intervals of length \(w\) is
\[
 S(w)=2\pi k+A\min(v,s). \tag{2}
\]
The complete periods have integral \(2\pi k\). The remaining arc can overlap one whole positive arc, or fit within it, according to its length. This supplies interval constraints simultaneously, including for overlapping intervals or variable-width level sets. The older periodization bound on the total positive exterior area did not use the interval lengths.

For scale comparison in the straight coordinate \(y=e^Lw/H\), the length-\(s\) interval in (2) requires a numerator of at least
\[
 C_*=\frac{2\pi}{s}\,\frac{L-\log H+\log s+1.090}{L}.
\]
At \(L=116\) this is \(1.5011380365588108\) to the displayed precision. On the first angular period this is the worst interval whenever \(\log y+1.090>1\). Before \(w=s\) the product \((S(w)/w)(\log y+1.090)\) increases; after it the product decreases. The corresponding Fourier coefficient of \(P_b\) at the first harmonic has modulus \(2\sin b/s=0.61846541097923\ldots\). This harmonic sits exactly at the bandwidth endpoint in (1).

## The actual arithmetic coordinate

Let \(R=10^{-4},\ \eta=1.090\). On \(e^{c-R}\le t\le e^{c+R}\) put
\[
 d\mu(t)=\frac{e^{-(\log t-c)/2}}{\log t}\,
          P_b\!\left(H(\log t-c)\right)\,dt,                         \tag{3}
\]
and set the measure to zero outside. For every \(115.05\le L\le116\) this measure vanishes in the target, and for **every** arithmetic interval \(J\) of length \(y\ge e^{50}\),
\[
 \mu(J)\le \frac{1.9992\,y}{\log y+\eta}.
 \tag{4}
\]
At \(L=116\) the factor \(1.50137\) suffices instead. This comparison concerns exactly the scale range and logarithmic denominator of the [proved sieve input](../../round3/low/FAREY.md).

Clip \(J\) to the support first. For an interval there of length \(y'\) and angular length \(w\), \(e^{c-R}w/H\le y'\le e^{c+R}w/H\), and its mass is at most \(e^{c+R/2}S(w)/(H(c-R))\). For \(y'\ge e^{50}\), a valid numerator is therefore
\[
 \frac{e^{3R/2}}{c-R}\frac{S(w)}w
       \left(c+R-\log H+\log w+\eta\right).                         \tag{5}
\]
If \(w\le 2\pi\), maximize at \(s\) as above. If \(w\ge2\pi\), then \(S(w)/w\le4\pi/(2\pi+s)\): each period has its maximum at \(2\pi k+s\), and \(2\pi(k+1)/(2\pi k+s)\) decreases with \(k\). The logarithmic term in (5) is at most \(c+R+\log(2R)+\eta\). For \(y'<e^{50}\) use the ordinary density bound \(e^{R/2}A/(c-R)\) from (3). Multiply it by \(50+\eta\) to cover clipping a longer interval to a short one; \(y/(\log y+\eta)\) increases for \(y\ge e^{50}\). The [192-bit calculation](dual_sieve.py) bounds these three expressions on 950 cells of width \(0.001\) by \(1.999183993\), and at \(L=116\) by \(1.501366196\). In each cell it puts the lower and upper endpoints into the factors according to their individual monotonicities.

One can even impose integer support. Let \(M(t)=\mu((-\infty,t])\) and select the integers \(m\) for which \(\lfloor M(m)\rfloor-\lfloor M(m-1)\rfloor=1\). The continuous density everywhere is \(<0.03\), so all the increments are zero or one. For half-open real intervals the counting discrepancy is less than \(3\), since the cumulative counts equal \(\lfloor M(\lfloor t\rfloor)\rfloor\) and each cumulative error has magnitude below \(1.03\). Closed intervals follow by expanding the endpoints. Discard any selected integers in the open gap and outside the support of (3). At most two points are lost: a selected point must follow some positive mass in its immediately preceding unit interval, and the open gap and the support each have only one relevant left-to-right exit from positive mass. Counts can only decrease. For \(y\ge e^{50}\), \(3(\log y+\eta)/y<10^{-6}\). Thus the resulting integer set obeys the original numerator \(2\) everywhere, and even the numerator \(1.502\) at \(L=116\). For \(y<e^{50}\) it obeys integer counting, and also classical \(2y/\log y\) when \(y\ge e^2\): the continuous density bound plus \(3\) gives this for \(y\ge1000\) using \(2/\log y\ge.04\), and for \(e^2\le y<1000\) the same inequality follows from \(0.03y+3\le 2y/\log y\) (on \([e^2,16]\) use monotonicity of \(2y/\log y\) and at most \(3.48\); on \([16,1000]\) use \(2/\log1000>.28\)). The written comparisons use the actual unrounded density \(e^{R/2}A/(c-R)<.023\).

Under the prime weight the square-root factor and Jacobian in (3) cancel *exactly*:
\[
 \frac H{e^{c/2}}\int \frac{\log t}{\sqrt t}
       g(H(\log t-c))\,d\mu(t)
     =\int_{|u|\le HR} g(u)P_b(u)\,du .
\]
The difference from \(\int_{\mathbb R}g\) is at most \(A\int_{|u|> HR}|g(u)|\,du\) by (1). A Gaussian multiplier \(e^{-(Qu/H)^2}\) in the arithmetic test costs at most another \(A\int_{\mathbb R}|g(u)|(1-e^{-(Qu/H)^2})\,du\). For the [previous signed kernel](../../lower/PROOF.md), \(Q=10^4,\ a<\pi\), these two absolute errors without \(A\) are at most \(4/[HR(1-(a/(HR))^2)]\) and \(16\sqrt\pi Q/H\), respectively. The first uses \(|g(u)|\le2/(u^2-a^2)\); the second uses \(u^2|g(u)|\le8\). After rounding, the cumulative discrepancy is below \(4\). An absolutely continuous compactly supported arithmetic test \(W(t)\) consequently incurs an additional error at most \(4\int |W'(t)|dt\) in the unnormalized arithmetic sum by integration by parts.

Equation (1) rules out distinguishing the gap by *any* exactly bandlimited test using only this angular mean. Equations (3)–(5) show why retaining the full local Brun–Titchmarsh denominator in this model does not remove the obstruction. For localized smoothed tests the stated quantitative errors control the comparison. Extra information on actual primes, arithmetic residue classes, or spectral information across the endpoint can distinguish the model. A [compact-height zero criterion](NEAR_HEIGHT.md) quantifies one such alternative.

## The correlated-neighbor denominator

The [stronger sieve inequality](CORRELATED_FAREY.md) has \(\eta=1.1328\) for \(y\ge e^{70}\). For this inequality the same continuous and integer models obey all interval bounds throughout \(115.050\le L\le116\). This is the earliest starting point on the \(0.001\) grid for a contiguous comparison up to 116 using this model. At the preceding grid point \(L=115.049\) the model itself violates the stronger inequality. These statements concern the model rather than the prime existence theorem.

For an angular interval contained in one window of length \(w\le2\pi\), put \(v=\log t-c,\ v_-\le v\le v_+\). In the ratio of its mass to its arithmetic length, the factor \(e^{-v/2}/(c+v)\) in (3) is at most \(e^{R/2}/(c-R)\). The change of variable \(dt=e^{c+v}du/H\) costs at most \(e^{v_+-v_-}\le e^{2\pi/H}\) when comparing the weighted average of \(P_b\) to its angular average. Thus the primary term (5) can use \(e^{R/2+2\pi/H}/(c-R)\) in place of \(e^{3R/2}/(c-R)\). The multi-period estimate stays as written, and the clipping case uses \(70+\eta\). The [same verifier](dual_sieve.py) retains the former constants and checks the stronger inequality on the same 950 cells: the continuous numerator is below \(1.99995310\) throughout, and below \(1.50193371\) at \(L=116\). The integer rounding adds less than \(10^{-20}\) to the numerator at \(y\ge e^{70}\), so the numerator \(1.502\) still suffices at 116. For the old bound on \(e^{50}\le y<e^{70}\) its earlier comparison still applies.

At \(L=115.049\) use the first full positive arc \(b\le u\le b+s\), which lies inside the support of (3). Put \(v_1=(b+s)/H\), \(\ell=c+b/H+\log s-\log H\). Its arithmetic length \(y\) satisfies \(\log y\ge\ell>70\). Its density is at least \(A e^{-v_1/2}/(c+v_1)\) almost everywhere on this arc. Its required sieve numerator is therefore at least
\[
 \frac{A e^{-v_1/2}}{c+v_1}(\ell+\eta)>2.00060571.
\]
The integer rounding changes any interval count by at most eight, by the cumulative discrepancy estimate above. Since \(8(\ell+\eta)e^{-\ell}<10^{-20}\) and \((\log y+\eta)/y\) decreases here, the integer model also violates this interval bound at \(115.049\).

Project attribution to Claude and Codex. Codex developed the interval-capacity comparison and its transfer in this workstream.
