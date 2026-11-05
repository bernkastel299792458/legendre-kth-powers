# Superseded certificates (do not use)

These certificates were produced with the KLN zero-density constants 17.253 / 5.663 (σ > 0.6), as quoted in Lee (2026) eq. (2.7).
The source verification (`../../input_verification/report_density.md`) found two problems with those constants:
- they come from Kadiri–Lumley–Ng (2018), whose computation relies on Hiary's bound, which Johnston–Yang (2023) call unreliable;
- they are **not** established for σ ∈ (0.997, 1).

The current certificates use the corrected Johnston–Yang (2023) values (C₁ ≤ 17.418, C₂ ≤ 2.231) for σ ∈ [0.98, 1), with σ₁ = 0.98.
