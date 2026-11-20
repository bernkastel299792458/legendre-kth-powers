# Removing full regions of semiprime moduli from the middle phase problem

Let \(Y=e^{70.7}, X=e^{c+2r}, Q=210,\ z=1732099\sqrt{e^{116}/H}\). Use [the remaining normalized signed problem](REMAINING_PHASE.md). For every contributing semiprime \(Y<q\le X/23\), one has \(q=pr\) for distinct primes \(p,r\le z\), neither dividing \(Q\). Indeed nonsquarefree moduli do not occur, \(Y>z\) precludes a divisor \(\lambda_q\), and \((p,r),(r,p)\) are the only remaining pairs. Thus \(B_z(q)=2|\lambda_p\lambda_r|>0\) on this entire class. Each table concerns the full middle-frequency contribution, including all ratios \(p/r\).

| Selected semiprime region | Actual-multiple upper | Main term plus low-mode subtraction, certified lower | Middle signed upper |
|---|---:|---:|---:|
| \(X/121<q\le X/23\), 48 logarithmic cells | .000785859 | .000147780 | .000638079 |
| \(X/400<q\le X/23\), 64 cells | .001764351 | .000367643 | .001396708 |
| \(X/750<q\le X/23\), 96 cells | .002451873 | .000537881 | .001913992 |
| \(X/1100<q\le X/23\), 96 cells | .002953449 | .000647603 | .002305846 |
| \(X/5000<q\le X/23\), 96 cells | .005561438 | .001216869 | .004344569 |

| Independently selected low semiprime region | Whole signed middle upper |
|---|---:|
| \(Y<q\le e^{80}\) | .000255361 |
| \(Y<q\le e^{82}\) | .001553842 |
| \(Y<q\le e^{83}\) | .003828252 |

Taking both \(Y<q\le e^{80}\) and \(X/400<q\le X/23\) removes their union from the problem and leaves a sufficient allowance **.00071653** for all other middle terms. At \(X/5000\) or \(e^{83}\) the respective stand-alone upper bound already exceeds the available .00236860. This procedure does not resolve all intermediate semiprimes.

**Prime rows.** The ranges used are inside \(599\le t\le2.169\,10^{25}\), where \(|\vartheta(t)-t|\le E(t)=\sqrt t\log^2(t)/(8\pi)\). Consequently \(l<p\le h\) has prime count \(\le(h-l+2E(h))/\log l\). Integrating \(\vartheta(t)\) by parts gives upper and lower harmonic bounds \([\log(h/l)+2E(h)/l]/\log l\) and \(\max(0,[\log(h/l)-2E(h)/l]/\log h)\), respectively. Open or closed artificial endpoints in upper counts can cost an extra one, absorbed by the error term using a one-sided limit or added explicitly. [Johnston, Proposition 3.1](https://arxiv.org/pdf/2109.02249)

**Upper physical charge.** For a positive integer cutoff \(m\) use \(X/m<q\le X/23\). Every near-region contribution has \(kq\in(X_-,X)\), \(X_-=e^{c-2r}\). Thus only \(23\le k<m,(k,210)=1\) occur. All factors belong to \([z/m,z]\), partitioned into the indicated number of equally spaced logarithmic cells. In an outer cell \((l,h]\) use \(l'=\max(l,X_-/(kz))\). Denote by \(H_p,N_p\) the harmonic and ordinary prime upper bounds on \((l',h]\). The inner prime count on a physical interval of length \(y\) has span at most \(y/(kp)\). For width \(v\) it is bounded by the tangent to \(2v/\log v\) at \(v_0\) whenever \(v\ge e^2\), by concavity and Brun–Titchmarsh; for smaller \(v\) the tangent intercept \(2v_0/\log^2v_0>10\) suffices. Set \(L_F=XA/H+2\delta S,\ v_0=L_F H_p/(k S N_p)\). Integrating the affine bound on each superlevel and summing the primes now gives \(2L_F H_p/(k\log v_0)\). This optimization uses upper bounds on both \(H_p,N_p\), which is valid because both coefficients of the tangent are nonnegative.

On this cell the factors \(G_{Qp}(z/p)\) and \(G_{Qr}(z/r)\) are bounded above by \(G_Q(z/l')\) and \(G_Q(zkh/X_-)\). Their arguments are at most the supplied integer cutoff, so these expressions use exact squarefree divisor sums. Also \(\rho(p)\rho(r)\le(p_{\min}/(p_{\min}-1))^2\), \(p_{\min}=X_-/(mz)\). The remaining multiplicative normalization is \(P_0/G_Q(z)^2\). Each unordered pair is included twice by summing the outer and inner indices; including the diagonal here is a positive enlargement. [Montgomery and Vaughan, Theorem 2](https://doi.org/10.1112/S0025579300004708)

**Subtracting the actual main and low phases.** For the contribution of this positive family to the middle band, the complementary mean and low-mode multiplier at \((p,r,t)\) is
\[
 \eta+\frac2Q \sum_{n\le Qpr/X} c_Q(n)\cos(2\pi n t/(Qpr)).
\]
It is positive for every \(pr\le X/23\), since \(\sum_{n\le9}|c_Q(n)|<24=\varphi(Q)/2\). For an outer cell \((l,h]\), truncate the inner cell to lie inside \((X/(ml),X/(23h)]\), which keeps every retained pair in the indicated \(q\)-region. On each product cell the code encloses the cosine over \(X_-\le t\le X\), all endpoint combinations and all possible \(n\), allowing zero if that \(n\) is not always active. Multiply the lower bound by the two harmonic prime lower bounds and \(G_Q(z/h)G_Q(z/r_{\mathrm{hi}})\); here all primes exceed the divisor arguments. Removing all \(p=r\) costs at most \(G_Q(m)^2(1+\eta)/(p_{\min}-1)\) by \(\sum_{n\ge p_{\min}}n^{-2}\le1/(p_{\min}-1)\). The smooth physical mass is at least \(e^{c-r}[A-4/(Hr(1-(a/(Hr))^2))]/H\). Upper and lower bounds for \(G_Q(z)\) use the [finite Euler convolution estimate](../../round7/physical/odd_sieve.py). Recombination into prime counts removes all nonzero modes; to isolate the middle one adds the previous upper diagonal absolute tail, \(<2.03\,10^{-13}\).

**Small end.** Here \(Qq<X\), so there are no low modes to put back. The periodic count of integers coprime to \(210\), minus its linear mean, has total oscillation \(106/35\) over one period; this follows by checking the two ends of each unit cell. Hence each real interval has this absolute discrepancy independently of its length. The normalized total remainder for each \(q\) costs at most \(P_0 S(106/35) B_z(q)\), also after taking the probability convolution defining the spline. For the total coefficient sum take logarithmic prime cells of maximum width .1, restrict both sides by the lower/upper hyperbolic cuts, and use the stated finite-\(\vartheta\) count in every projected interval. The upper coefficient is computed from \(G_Q(z/p)\) exactly up to 4096 and by its finite convolution upper bound beyond, capped by the original \(|\lambda_p|\le1\). Add the high diagonal upper bound to isolate the middle.

~~~powershell
python -B round8/physical_low/semiprime_annulus.py --end 400 --cells 64 --upper .001396708
python -B round8/physical_low/semiprime_annulus.py --end 1100 --cells 96 --upper .002305846
python -B round8/physical_low/semiprime_small.py --logend 80 --upper .000255361
~~~
