import Mathlib

/-!
# Basic physical constants

Only the *positivity* of the Boltzmann constant is ever used in the proofs;
the numerical value is recorded for documentation.
-/

noncomputable section

namespace ExoLean

/-- Boltzmann constant in SI units (J K⁻¹). -/
def kB : ℝ := 1.380649e-23

theorem kB_pos : 0 < kB := by norm_num [kB]

theorem kB_ne_zero : kB ≠ 0 := kB_pos.ne'

/-- The Euler–Mascheroni constant `γ ≈ 0.5772`, which appears in the analytic
transit-radius formula of Heng & Kitzmann (2017). -/
abbrev γE : ℝ := Real.eulerMascheroniConstant

end ExoLean
