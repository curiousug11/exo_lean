import ExoLean.OpenProblems

/-!
# Target 1: does the spectrum determine the density profiles?

* `not_densityProfilesIdentifiable`: **the original Target 1 is false for every cross-section
  set**. It allowed a zero-thickness column (`R0 = Rtop`), whose transit radius is just `R0`
  whatever the atmosphere. Pointwise modifications of a discontinuous mixing ratio are
  another way it fails. The corrected target `DensityProfilesIdentifiableCts` therefore asks
  for `R0 < Rtop` and continuous profiles.
* `not_densityProfilesIdentifiableCts_of_proportional`: **the corrected target is still false
  whenever two species have proportional cross-sections on the observed band** (for example
  two grey absorbers, or an absorber and an isotopologue with the same band shape). Moving
  column density from one species to the other, in the ratio of their cross-sections, leaves
  the extinction field unchanged at every observed wavelength. The counterexample uses
  constant, physically admissible mixing ratios.

The remaining open case is a single species, or species whose cross-sections are not
proportional. There a different obstruction is expected. For one species, the spectrum
`R_p² = R0² + 2∫ b (1 − e^{−σ N(b)}) db` is a Laplace-type transform of the *distribution* of
the column density `N(b)`. So it can determine `N` only up to rearrangement, and uniqueness
requires something like monotonicity of `N`.
-/

noncomputable section

open Real

namespace ExoLean

open OpenProblems

variable {ι : Type*} [Fintype ι]

namespace Atmosphere

/-- The spectrum at a wavelength `w` depends only on the extinction profile at `w`. -/
theorem spectrum_apply_eq_of_extinction_eq {σ : ι → ℝ → ℝ} {A B : Atmosphere ι}
    (hR : A.R0 = B.R0) {w : ℝ} (h : ∀ r, A.extinction σ r w = B.extinction σ r w)
    (Rtop : ℝ) : A.spectrum σ Rtop w = B.spectrum σ Rtop w := by
  simp only [spectrum, transitRadius, slantOpticalDepth, hR, h]

/-- The atmosphere with unit `P0, g, m, T`, reference radius `R0` and given mixing ratios. -/
def unitAtm (R0 : ℝ) (X : ι → ℝ → ℝ) : Atmosphere ι := ⟨R0, 1, 1, 1, fun _ => 1, X⟩

omit [Fintype ι] in
theorem unitAtm_wellPosed (R0 : ℝ) (X : ι → ℝ → ℝ) : (unitAtm R0 X).WellPosed :=
  ⟨one_pos, one_pos, one_pos, fun _ => one_pos, continuous_const⟩

omit [Fintype ι] in
theorem unitAtm_numberDensity_pos (R0 : ℝ) (X : ι → ℝ → ℝ) (r : ℝ) :
    0 < (unitAtm R0 X).numberDensity r :=
  (unitAtm_wellPosed R0 X).numberDensity_pos r

omit [Fintype ι] in
/-- The number density of `unitAtm` does not depend on the mixing ratios. -/
theorem unitAtm_numberDensity (R0 : ℝ) (X Y : ι → ℝ → ℝ) :
    (unitAtm R0 X).numberDensity = (unitAtm R0 Y).numberDensity := rfl

end Atmosphere

open Atmosphere

/-- **The original Target 1 is false**, for every cross-section set, top radius and band. -/
theorem not_densityProfilesIdentifiable [Nonempty ι] (σ : ι → ℝ → ℝ) (Rtop : ℝ) (S : Set ℝ) :
    ¬ DensityProfilesIdentifiable σ Rtop S := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hspec : ∀ w ∈ S, (unitAtm Rtop fun _ _ => 0).spectrum σ Rtop w =
      (unitAtm Rtop fun _ _ => 1).spectrum σ Rtop w := fun w _ => by
    simp [Atmosphere.spectrum, ExoLean.transitRadius, unitAtm]
  have := h (unitAtm Rtop fun _ _ => 0) (unitAtm Rtop fun _ _ => 1)
    (unitAtm_wellPosed _ _) (unitAtm_wellPosed _ _) rfl hspec i Rtop
    ⟨le_rfl, le_rfl⟩
  simp only [speciesDensity, unitAtm, zero_mul, one_mul] at this
  exact (unitAtm_numberDensity_pos Rtop (fun _ _ => (1 : ℝ)) Rtop).ne' (this.symm.trans rfl)

/-- **The corrected Target 1 fails for proportional cross-sections.** If `σⱼ = k σᵢ` on the
band `S` (`i ≠ j`, `k > 0`), the atmosphere with `Xᵢ = k/(1+k)` and the atmosphere with
`Xⱼ = 1/(1+k)` (all other species absent, all profiles constant) have identical spectra on `S`
but different density profiles. -/
theorem not_densityProfilesIdentifiableCts_of_proportional {σ : ι → ℝ → ℝ} {S : Set ℝ}
    {i j : ι} (hij : i ≠ j) {k : ℝ} (hk : 0 < k) (hprop : ∀ w ∈ S, σ j w = k * σ i w)
    (Rtop : ℝ) : ¬ DensityProfilesIdentifiableCts σ Rtop S := by
  classical
  intro h
  set XA : ι → ℝ → ℝ := fun l _ => if l = i then k / (1 + k) else 0
  set XB : ι → ℝ → ℝ := fun l _ => if l = j then 1 / (1 + k) else 0
  set A := unitAtm (Rtop - 1) XA
  set B := unitAtm (Rtop - 1) XB
  have hn : B.numberDensity = A.numberDensity := unitAtm_numberDensity _ _ _
  have hspec : ∀ w ∈ S, A.spectrum σ Rtop w = B.spectrum σ Rtop w := fun w hw =>
    spectrum_apply_eq_of_extinction_eq (σ := σ) (A := A) (B := B) (w := w) rfl (fun r => by
      simp only [extinction, speciesDensity, hn]
      simp only [A, B, unitAtm, XA, XB, ite_mul, zero_mul, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hprop w hw]
      ring) Rtop
  have := h A B (unitAtm_wellPosed _ _) (unitAtm_wellPosed _ _) rfl (by simp [A, unitAtm])
    (fun _ => continuous_const) (fun _ => continuous_const) hspec i Rtop
    ⟨by simp [A, unitAtm], le_rfl⟩
  simp only [speciesDensity, A, B, unitAtm, XA, XB, hij, ↓reduceIte] at this
  have hpos := unitAtm_numberDensity_pos (Rtop - 1) XA Rtop
  have : k / (1 + k) = 0 := by
    have h2 := this
    simp only [zero_mul] at h2
    exact (mul_eq_zero.mp h2).resolve_right hpos.ne'
  have : 0 < k / (1 + k) := by positivity
  linarith

end ExoLean
