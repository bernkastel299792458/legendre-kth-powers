# Formalization status

**The end-to-end Lean proof requested for the conditional k=6 theorem is not
complete.** The repository distinguishes a complete written, computer-assisted
argument from the portions actually checked by Lean's kernel. A successful
build of the present sources is not an H1+H2-only proof.

## Kernel-checked components

- Exact sixth-power algebra and strict endpoint reductions.
- The actual primality of all 1259 small-range witnesses, via 5349 recursive
  Lucas/Pratt nodes. This component does not assume Sorenson–Webster or trust
  the Python generator's primality decisions.
- The CHL integer ranges and exponential thresholds, with real exponentials
  proved by Mathlib's reflective interval tactic. Given the explicitly stated
  CHL literature rows, these establish the entire lower range through
  n = 1242317999994 and its overlap with L = 167.
- Exact rational checks and continuous real-parameter coverage of the 94 new
  and 60 inherited cells; saved rational maxima, margins, and 6% scaling.
- Four-point quadratic/affine identities; the exact exponential sigma-weight
  integral; common zero-weight domination and coefficient-scaling algebra.
- The six-term tail's numerical threshold, proved using kernel-checked exp/log
  bounds, and its analytic decay on the entire range L >= 700.
- Finite von Mangoldt weighted-sum extraction of an interior prime, given
  the explicitly stated weighted lower bound and support conditions.
- Final assembly **conditional on the three explicit analytic segment
  conclusions**. Its name is `sixth_powers_of_segment_inputs`, and its complete
  type exposes these extra inputs.

The final build report identifies which of these source files were actually
compiled. `#print axioms` must be read together with `#check`: an extra local
conclusion supplied as a theorem argument does not appear as a custom axiom.

## Remaining end-to-end obligations

1. A multiplicity-aware formal zero-counting interface for the actual Riemann
   zeta function, with exact translations of H1, H2, finite-height RH, and the
   cited classical inputs. H1/H2 are accepted mathematical inputs; they are
   not tasks to re-prove here.
2. The integrated explicit formula and its lawful pairing with the trapezoid
   and polynomial weights, including convergence, distributional endpoint
   atoms, and Mellin-transform bounds.
3. The zero-density layer integral, Stieltjes upper sums, finite-height split,
   and the analytic height tails as bounds for the actual zero contributions.
4. Kernel-checkable transcendental enclosures for the complete 94-cell and
   60-cell sums. The existing Arb replays establish these computationally,
   but importing their saved rational outputs does not establish this bridge
   in Lean. The rational coverage theorems deliberately do not claim it.
5. The prime-power and trivial-zero budgets linked to the actual weighted
   von Mangoldt sums, and the CHJII truncation estimate linked to the actual
   zeta zeros. The proved scalar tail bound does not itself supply this link.

The unresolved obligations are not hidden behind renamed QRH/CS assumptions,
axioms, `sorry`, `native_decide`, or a blanket claim that a certificate is sound.
The paper contains the human-readable arguments; a future formalization must
produce the missing proof terms before this status can be upgraded.

## Reading the result correctly

`CHLRows -> AnalyticSegmentInputs -> SixthPowerConclusion` is an honest
assembly theorem. It is weaker as a formalization claim than the requested
H1/H2 + named literature inputs -> SixthPowerConclusion. A standard-axioms-only
audit of the former does not turn it into the latter.
