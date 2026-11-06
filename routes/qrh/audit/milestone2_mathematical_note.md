# Formalization note: a conservative certificate for the difficult middle cell

**Milestone 2 note, 2026-11-06.** The analytic reduction, numerical certificate,
and final prime theorem have compiled. Actual proof-dependency and axiom
checks passed. This result covers this pilot cell; full k=6 formalization
remains incomplete.

Fix A=715/4, C=179, and any L in [A,C]. Put x=exp(L), h=6 exp(5L/6),
a=1/32, b=31/32 and q=1+exp(C/6)/6. Every zero sum below counts the actual
analytic multiplicity of a nontrivial zero of Mathlib's Riemann zeta function.
The accepted external inputs for this cell are QRH(7/8), CS v2, Rosser's count,
and the classical integrated explicit formula. The original unweighted
integrated formula, rather than a project-specific weighted estimate, is the
last of these inputs.

## Four-point calculation

For a function G, define

\[
 D G=\frac{G(x)-G(x+ah)-G(x+bh)+G(x+h)}{abh}.
\]

With G_rho(t)=t^(rho+1)/(rho(rho+1)), ordinary differentiation and the norm
mean-value inequality prove the three original kernel bounds:

\[
 |D G_\rho|\le h x^{\beta-1}
 \min\{1,(2/b)q/|\gamma|,(4/(ab))q^2/|\gamma|^2\}.
\]

This proof uses the actual complex powers. The base bound does not require
gamma to be nonzero, so it also controls the trivial-zero primitives.
Their geometric majorant proves summability, justifies the four finite
operations on their sum, and gives h x^(-3)/(1-x^(-2)).

Applying the four-point operation to the classical height-truncation limits
is a finite operation on limits. The quadratic term gives h; both affine
terms cancel. The finite sum defining the integrated Chebyshev function
gives the actual trapezoid-weighted von Mangoldt sum. Nonnegative weights,
their bound 1/b, zero endpoint values and strict interior support are all
proved directly. A positive weighted prime contribution therefore produces
an actual prime strictly between x and x+h.

## Finite real-part and height grids

Let s_j=(2048+j)/4096 for 0<=j<=1536. A direct telescoping staircase estimate
gives the same exact exponential weights as the original layer integral:

\[
 w_j=e^{(s_{j+1}-1)A}-e^{(s_j-1)A}.
\]

The actual positive-height cumulative weight is bounded by the explicit
Phi_A(u) at height exp(u), using the original CS row at s_j and Rosser for
the base count. Closed sigma endpoints are included in the finite count.

The log-height nodes are u_i=(1841+i)/64 for 0<=i<=988, with U=u_988.
The first node exceeds log(3e12), and the kernel g is still 1 there. Thus
this pilot needs no finite-height RH input. Finite telescoping bounds every
actual truncated positive-height sum by

\[
 \sum_{i=0}^{987}(g(e^{u_i})-g(e^{u_{i+1}}))\Phi_A(u_{i+1})
 +\sum_{0<\gamma\le T}m_\rho e^{(\beta-1)A}g(\max\{\gamma,e^U\}).
\]

The second sum is essential: zeros below exp(U) still have residual weight.

## A different, conservative height tail

The Lean pilot uses a geometric bound in place of the original paper's
improper-integral tail. For U>=6 and v>=0, logarithmic concavity gives

\[
 \Phi_A(U+v)\le e^{3v/2}\Phi_A(U).
\]

Indeed, each component is a nonnegative multiple of exp(pu)u^r with
p<=1 and 0<=r<=3; the logarithmic factor grows by at most exp(rv/U).
At heights exp(U)4^k, the cumulative envelope thus grows by at most 8^k.
The quadratic kernel decays by 16^k. Finite prefix-count summation yields
the following bound for the full residual, including lower heights:

\[
 16 R_2 q^2 e^{-2U}\Phi_A(U),\qquad R_2=4096/31.
\]

Actual conjugation and multiplicity symmetry double the complete
positive-height expression. The tail in the total budget is therefore
32 R_2 q^2 exp(-2U) Phi_A(U). This is a newly certified conservative
expression, not an assertion that the frozen certificate used this tail.

## Positive moments instead of a large exponential matrix

For the moment sums, use the right-endpoint heights
t_i=u_(i+1)=(1842+i)/64 for 0<=i<=987. Write
p_j=3(1-s_j)/(2-s_j), v_i=t_i+log(t_i), p0=1/3 and v0=2057/64.
The first grid node u_0 is used by the kernel mass, not as a moment height.
The exact factorization

\[
 e^{p_jv_i}=e^{p_jv_0}e^{p_0(v_i-v_0)}
             e^{(p_j-p_0)(v_i-v_0)}
\]

has 0<=(p_j-p0)(v_i-v0)<=11 throughout both finite grids. Mathlib's proved
exponential remainder bound implies

\[
 e^z\le\sum_{d=0}^{20}\frac{z^d}{d!}+\frac{2z^{21}}{21!}
 \quad(0\le z\le11).
\]

Nonnegative finite sums can now be exchanged, giving products of two
moment families. Each real factor is bounded by a dyadic rational
with denominator 2^48. The integer moment of pairs (c_j,a_j) is
sum_j c_j a_j^d; division by 2^(48(d+1)) is proved to equal the corresponding
real moment. No empirical success flag is a hypothesis of these identities.

The proved final rational checks are a main moment bound <=3759/4000,
an auxiliary bound <=1/50000, and prime-power/trivial-zero bounds each
<=1/1000000. Their sum is 469886/500000=0.939772, below 47/50.
All four bounds and the final theorem have compiled. The actual final
proof uses them to discharge the numerical premise. Both its complete
type and its actual proof dependencies are printed in
[milestone2_dependencies.txt](milestone2_dependencies.txt).

## Review status and AI use

Codex agents implemented the Lean arguments and generated candidate
certificates; a separate Codex agent reviewed portions it did not implement.
The review identifies its self-reviewed portions explicitly. This is not
human peer review, and Claude's historical review is not presented as a
review of these new formalization modules. Original source formulae and
their external status remain listed in the interface and review records.
