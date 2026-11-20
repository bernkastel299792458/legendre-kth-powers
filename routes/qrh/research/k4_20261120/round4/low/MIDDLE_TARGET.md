# The right-boundary target at \(\log x=160\)

For the [modulus-six detector](../euler/PROOF.md), a uniform right-boundary coefficient **\(K_3\le0.00270\)**, with the same frozen mollifier and left boundary below, would prove the prime-interval statement for every \(L=\log x\ge160\). This improved coefficient has not been proved. The current direct coprime high-norm analysis yields \(K_3<0.010235725\) for these parameters.

Use \(Q=m=6,\ \delta=.9,\ W=9.6,\ \log h=-2.8,\ U=160/4-1.02\), the standard mean-value window, and the split-left \(Q=6\) fourth moment. The weighted boundary inequalities and the value \(K_1<0.230590216\) apply for every \(T\ge e^U\); the required better \(K_3\) must be uniform over that same height range. Keep the spectral staircase and all horizontal real-part nodes from the existing implementation.

For each moment term, write \(s\) for its real-part node,
\[
 p=\frac{3(1-s)}{2-s},\qquad k=\frac{3\delta(2s-1)}{(2-s)^2},
 \qquad c=\frac{3\delta}{2-s}.
\]
All dependence on \(K_3\) in this term is through
\[
 K_3(K_1/K_3)^p
 \exp\left(\frac{k\{U+\log(UK_1/K_3)\}}{U+c}\right).
\]
Thus scaling \(K_3\) by \(b\) multiplies the term by \(b^{1-p-k/(U+c)}\). Each exponent is positive, and each moment term has positive coefficient. Reducing \(K_3\) preserves the height-correction condition \(c+1+c/U<\log(UK_1/K_3)\). The fixed portion, which includes the base count, all rectangle edges, prime powers and trivial zeros, is less than \(0.007128798\). All half-line decay tests from the original verification still apply.

| Uniform \(K_3\) used | Normalized budget at 160 |
|---|---:|
| \(0.0110277452602541\ldots\), variance calculation | \(2.2664164864\ldots\) |
| \(0.0102357245134621\ldots\), direct high norm | \(2.1698216198\ldots\) |
| \(0.00275\), hypothetical | \(1.0089179679\ldots\) |
| \(0.00270\), hypothetical | \(0.9982253985\ldots\) |

The [192-bit verifier](middle_target.py) extracts all moment coefficients, obtains the fixed costs from the complete detector budget, and bisects this monotone scalar expression. Its exact threshold lies strictly between \(0.00270827204207624\) and \(0.00270827204208629\). This is about \(26.46\%\) of the current direct high-norm coefficient. The number applies to this analytic budget and fixed parameters; a different detector, left moment, or height weighting has its own threshold. Reproduce with \(\texttt{python -B middle_target.py}\). Project attribution to Claude and Codex.

## The modulus-210 detector at the same anchor

Keep the parameters of the \(L=176\) certificate, with \(\delta=.92,\ W=9.5,\ \log h=-3.5\), the density mode of the folded mean, and both direct norm estimates. Set \(U=38.98\) for the new anchor \(L=160\). The script takes the fixed cost and all positive terms from the same full verification and applies the scaling formula above. In this case the fixed cost is less than \(0.007441939\), while \(K_1<.229030688\), \(K_3<.006438814\), and the computed total is less than \(1.708921576\). With the same left bound and detector, a uniform \(K_3\le .00255\) suffices for the entire half-line \(L\ge160\): the corresponding budget is below \(0.997511445\). At \(K_3=.00257\) the expression exceeds \(1.00203967\). The improved coefficient is an open target. Run \(\texttt{python -B middle_target.py --modulus 210}\).
