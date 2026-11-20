# Aggregating every pair with the same large squarefree modulus

Let \(B_z(q)=\sum_{d,e\le z,\,[d,e]=q}\lambda_d\lambda_e\). The following identity and domination apply to every \(q>z^2/3\). In particular they apply to every \(q>x\) when \(x=e^{116},\ z=3000000\sqrt{x/H}\). As usual put \(\lambda_n=0\) for \(n>z\), and \(G_v(t)=\sum_{k\le t,(k,v)=1}\mu^2(k)/\varphi(k)\).

For nonsquarefree \(q\), the coefficient is zero. For squarefree \(q\), all pairs have \((d,e)\le2\), since \(de=(d,e)q\le z^2\). If \(q\) is odd, each pair has \((d,e)=1\) and \(\lambda_d\lambda_e\) has sign \(\mu(q)\). If \(q=2r\) is even, removing the factor 2 gives an ordered factorization \(uv=r\), so \((u,v)=1\). There are three possible placements of 2: front, back, or both. Thus
\[
 B_z(2r)=\sum_{uv=r}\left[(\lambda_u+\lambda_{2u})(\lambda_v+\lambda_{2v})-\lambda_u\lambda_v\right].
\]
For odd squarefree \(u\), separating terms with a factor 2 in \(G_u\) gives
\[
 \lambda_u+\lambda_{2u}=\frac{\mu(u)\rho(u)}G
    \left(G_{2u}(z/u)-G_{2u}(z/(2u))\right).
\]
Hence \(A=|\lambda_u|\ge a=|\lambda_{2u}|\). Similarly \(D=|\lambda_v|\ge b=|\lambda_{2v}|\). The summand in \(B_z(2r)\) has sign \(-\mu(u)\mu(v)=\mu(q)\) whenever it is nonzero, and absolute value \(aD+Ab-ab\).

The signed coefficient therefore satisfies
\[
 B_z(q)=\mu(q)|B_z(q)|,\qquad
 G^2|B_z(q)|\ge
 \sum_{\substack{d,e\le z,\ de=q\\(d,e)=1}}
      \mu^2(d)\mu^2(e)\rho(d)\rho(e).
\]
For an odd modulus this follows from \(G|\lambda_d|\ge\rho(d)\) for squarefree \(d\le z\). For an even modulus, if \(2u,2v\le z\), the absolute value \(aD+Ab-ab\) is at least \(ab\ge4\rho(u)\rho(v)/G^2\), enough for the two coprime placements. If just \(2u\le z\), the absolute value is \(aD\); when \(v\le z\) this pays the one available term. If \(v>z\) there is no admissible placement. The reversed case follows by exchanging \(u,v\). This proves the bound termwise in \(uv=r\).

The [forward-lobe calculation](SPIKE_FLOOR.md) used only the right-hand side of the last displayed inequality. Consequently **after performing all same-modulus cancellation exactly**, the normalized mass of \(|B_z(q)|\) on that one lobe still exceeds **.0047443**, as compared with the ordinary main-term complement below **.004207**. One must retain cancellation between distinct moduli or couple this remainder to another part of the prime-interval inequality.

The same identities explain the remaining signed sum. On the dangerous right lobe only the first multiple is possible for \(q>x\), and the weight has the form \(\sum_q\mu(q)|B_z(q)|W(q)\) with \(W\ge0\). At fixed \(d\), exchanging \(q=de\) leaves \(e\) in a physical interval of relative width at most \(\exp((2\pi-a-K(c-L))/K)-1<1.08\,10^{-12}\). The full range of either variable is \(x/z<d,e\le z\), with \(57.45<\log d,\log e<58.55\). Even the more favorable uniform cumulative threshold \(4.430\,10^{-9}\) for \(\log Y\ge58\) costs more than 8100 interval lengths when the two endpoint errors are charged separately. This statement concerns the strength of the previously certified cumulative estimates, not the value of the short Möbius sum. A direct prefix-only inference cannot force cancellation here: a sequence bounded by one, supported and positive on that short interval, obeys the same cumulative error cap throughout the dyadic range. Multiplicativity or control of a new averaged short sum would be additional information.
