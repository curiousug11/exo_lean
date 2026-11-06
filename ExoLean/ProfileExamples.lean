import ExoLean.ProfileDegeneracy

/-!
# Explicit constructive counterexamples in the exact forward model

1. `Atmosphere.isothermal_twin`: isothermal + isochemical at `T0`, versus isothermal at `c T0`
   with mixing ratios depleted upward as `c X exp(-(1 - 1/c)(r - R0)/H)`.
2. `Atmosphere.exists_inverted_twin`: a normal (temperature decreasing outward) atmosphere
   and a thermally **inverted** atmosphere. Both are non-isothermal and hydrostatic, both
   have physically admissible mixing ratios, and they give identical transmission spectra
   for all cross-sections.
-/

noncomputable section

open Real

namespace ExoLean

namespace Atmosphere

variable {ι : Type*} {A : Atmosphere ι}

/-- Closed form of the compensating factor between two isothermal atmospheres. -/
theorem compensation_isothermal (hA : A.WellPosed) {T0 c : ℝ} (hT : ∀ r, A.T r = T0)
    (hc : 0 < c) (r : ℝ) :
    A.compensation (fun _ => c * T0) r =
      c * exp (-(r - A.R0) * (1 - c⁻¹) / (kB * T0 / (A.m * A.g))) := by
  have hT0 : 0 < T0 := hT A.R0 ▸ hA.T_pos A.R0
  have hm := hA.m_pos
  have hg := hA.g_pos
  have hk := kB_pos
  rw [compensation, pressure_of_isothermal hT,
    pressure_of_isothermal (A := A.withT fun _ => c * T0) (fun _ => rfl)]
  show c * T0 / A.T r * (A.P0 * exp (-(r - A.R0) / (kB * T0 / (A.m * A.g))) /
    (A.P0 * exp (-(r - A.R0) / (kB * (c * T0) / (A.m * A.g))))) = _
  rw [hT, mul_div_mul_left _ _ hA.P0_pos.ne', ← exp_sub, mul_div_cancel_right₀ _ hT0.ne']
  congr 2
  field_simp
  ring

/-- **Isothermal twin.** An isothermal, isochemical atmosphere at temperature `T0` and the
isothermal atmosphere at `c T0` with mixing ratios
`X'ᵢ(r) = c Xᵢ exp(-(1 - 1/c)(r - R0)/H)` have identical exact transmission spectra.
For `c ≠ 1` and an absorber with `Xᵢ ≠ 0`, the twin is **not** isochemical. -/
theorem isothermal_twin [Fintype ι] (hA : A.WellPosed) {T0 c : ℝ} (hT : ∀ r, A.T r = T0)
    {x : ι → ℝ} (hX : ∀ i r, A.X i r = x i) (hc : 0 < c) :
    let A' := A.retemper (fun _ => c * T0)
    A'.Isothermal ∧
    (∀ i r, A'.X i r = c * x i * exp (-(r - A.R0) * (1 - c⁻¹) / (kB * T0 / (A.m * A.g)))) ∧
    (∀ σ Rtop, A'.spectrum σ Rtop = A.spectrum σ Rtop) ∧
    (∀ i, x i ≠ 0 → c ≠ 1 → ¬ ∃ y, ∀ r, A'.X i r = y) := by
  have hT0 : 0 < T0 := hT A.R0 ▸ hA.T_pos A.R0
  have hpos : ∀ r : ℝ, 0 < (fun _ => c * T0) r := fun _ => mul_pos hc hT0
  refine ⟨⟨c * T0, fun _ => rfl⟩, ?_, spectrum_retemper hA hpos, ?_⟩
  · intro i r
    rw [retemper_X, compensation_isothermal hA hT hc, hX]
    ring
  · intro i hxi hc1 ⟨y, hy⟩
    have h0 := hy A.R0
    have h1 := hy (A.R0 + 1)
    rw [retemper_X, compensation_isothermal hA hT hc, hX] at h0 h1
    have hH : 0 < kB * T0 / (A.m * A.g) :=
      div_pos (mul_pos kB_pos hT0) (mul_pos hA.m_pos hA.g_pos)
    have hexp : exp (-(A.R0 + 1 - A.R0) * (1 - c⁻¹) / (kB * T0 / (A.m * A.g))) = 1 := by
      simp only [sub_self, neg_zero, zero_mul, zero_div, exp_zero, mul_one] at h0
      have h := h1.trans h0.symm
      have h' : x i * c * exp (-(A.R0 + 1 - A.R0) * (1 - c⁻¹) / (kB * T0 / (A.m * A.g))) =
          x i * c * 1 := by rw [mul_assoc, h, mul_one]
      exact mul_left_cancel₀ (mul_ne_zero hxi hc.ne') h'
    rw [exp_eq_one_iff, div_eq_zero_iff] at hexp
    rcases hexp with h | h
    · have : 1 - c⁻¹ = 0 := by
        have : (-(A.R0 + 1 - A.R0)) = -1 := by ring
        rw [this] at h; linarith
      have : c⁻¹ = 1 := by linarith
      exact hc1 (inv_eq_one.mp this)
    · exact hH.ne' h

/-! ### Normal versus thermally inverted atmospheres -/

/-- The logistic function `s(x) = 1/(1 + e^{-x})`, used to build smooth temperature profiles. -/
def logistic (x : ℝ) : ℝ := 1 / (1 + exp (-x))

theorem logistic_pos (x : ℝ) : 0 < logistic x := by
  unfold logistic; positivity

theorem logistic_lt_one (x : ℝ) : logistic x < 1 := by
  unfold logistic
  rw [div_lt_one (by positivity)]
  linarith [exp_pos (-x)]

theorem logistic_strictMono : StrictMono logistic := by
  intro x y hxy
  unfold logistic
  apply one_div_lt_one_div_of_lt (by positivity)
  have : exp (-y) < exp (-x) := exp_lt_exp.mpr (by linarith)
  linarith

theorem continuous_logistic : Continuous logistic := by
  unfold logistic
  exact continuous_const.div (continuous_const.add (continuous_neg.rexp))
    (fun x => by positivity)

/-- Temperature decreasing outward: `T0 + ΔT · s(-(r - R0)/L)`. -/
def Tnormal (T0 ΔT R0 L : ℝ) (r : ℝ) : ℝ := T0 + ΔT * logistic (-(r - R0) / L)

/-- Thermal inversion, temperature increasing outward: `T0 + ΔT · s((r - R0)/L)`. -/
def Tinverted (T0 ΔT R0 L : ℝ) (r : ℝ) : ℝ := T0 + ΔT * logistic ((r - R0) / L)

/-- The normal-profile atmosphere with constant mixing ratios `x`. -/
def normalAtm (R0 P0 g m T0 ΔT L : ℝ) (x : ι → ℝ) : Atmosphere ι :=
  ⟨R0, P0, g, m, Tnormal T0 ΔT R0 L, fun i _ => x i⟩

/-- **Constructive counterexample: thermal inversion is invisible.**
Fix any `R0, P0, g, m > 0`, `T0 > 0`, `0 < ΔT ≤ T0`, `L > 0`, and trace mixing ratios
`xᵢ ≥ 0` with `2 Σ xᵢ ≤ 1`. Then there are two atmospheres `A` and `A'`:
* `A` has the non-inverted profile `Tnormal` (strictly decreasing outward) and isochemical
  mixing ratios `x`;
* `A'` has the inverted profile `Tinverted` (strictly increasing outward) and the
  compensating mixing ratios.

Both are hydrostatic and well posed, both have admissible mixing ratios, neither is
isothermal, and their exact transmission spectra agree for **all** cross-sections and
truncation radii. -/
theorem exists_inverted_twin [Fintype ι] {R0 P0 g m T0 ΔT L : ℝ}
    (hP0 : 0 < P0) (hg : 0 < g) (hm : 0 < m) (hT0 : 0 < T0) (hΔ : 0 < ΔT) (hΔT0 : ΔT ≤ T0)
    (hL : 0 < L) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hxs : 2 * ∑ i, x i ≤ 1) :
    let A := normalAtm R0 P0 g m T0 ΔT L x
    let A' := A.retemper (Tinverted T0 ΔT R0 L)
    A.WellPosed ∧ A'.WellPosed ∧ A.PhysicalVMR ∧ A'.PhysicalVMR ∧
    StrictAnti A.T ∧ StrictMono A'.T ∧ ¬ A.Isothermal ∧ ¬ A'.Isothermal ∧
    ∀ σ Rtop, A'.spectrum σ Rtop = A.spectrum σ Rtop := by
  intro A A'
  -- monotonicity of the two profiles
  have hanti : StrictAnti (Tnormal T0 ΔT R0 L) := by
    intro a b hab
    simp only [Tnormal]
    have : -(b - R0) / L < -(a - R0) / L := by
      apply div_lt_div_of_pos_right _ hL; linarith
    nlinarith [logistic_strictMono this]
  have hmono : StrictMono (Tinverted T0 ΔT R0 L) := by
    intro a b hab
    simp only [Tinverted]
    have : (a - R0) / L < (b - R0) / L := div_lt_div_of_pos_right (by linarith) hL
    nlinarith [logistic_strictMono this]
  have hposN : ∀ r, 0 < Tnormal T0 ΔT R0 L r := fun r => by
    simp only [Tnormal]; nlinarith [logistic_pos (-(r - R0) / L)]
  have hposI : ∀ r, 0 < Tinverted T0 ΔT R0 L r := fun r => by
    simp only [Tinverted]; nlinarith [logistic_pos ((r - R0) / L)]
  have hcN : Continuous (Tnormal T0 ΔT R0 L) := by
    unfold Tnormal
    exact continuous_const.add (continuous_const.mul (continuous_logistic.comp (by fun_prop)))
  have hcI : Continuous (Tinverted T0 ΔT R0 L) := by
    unfold Tinverted
    exact continuous_const.add (continuous_const.mul (continuous_logistic.comp (by fun_prop)))
  have hA : A.WellPosed := ⟨hP0, hg, hm, hposN, hcN⟩
  have hvmr : A.PhysicalVMR := fun r _ => ⟨hx, by
    show ∑ i, x i ≤ 1
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hx i]⟩
  have notIso : ∀ f : ℝ → ℝ, (StrictMono f ∨ StrictAnti f) → ¬ ∃ T, ∀ r, f r = T := by
    rintro f hf ⟨T, hT⟩
    have h01 : f 0 = f 1 := (hT 0).trans (hT 1).symm
    rcases hf with hf | hf
    · exact absurd h01 (hf zero_lt_one).ne
    · exact absurd h01 (hf zero_lt_one).ne'
  refine ⟨hA, hA.retemper hcI hposI, hvmr, ?_, hanti, hmono, notIso _ (.inr hanti),
    notIso _ (.inl hmono), spectrum_retemper hA hposI⟩
  apply PhysicalVMR.retemper hA hvmr hcI hposI (c := 2)
  · -- normal ≤ inverted above R0
    intro s hs
    show Tnormal T0 ΔT R0 L s ≤ Tinverted T0 ΔT R0 L s
    simp only [Tnormal, Tinverted]
    have hs' : R0 ≤ s := hs
    have : -(s - R0) / L ≤ (s - R0) / L := by
      apply div_le_div_of_nonneg_right _ hL.le; linarith
    nlinarith [logistic_strictMono.monotone this]
  · -- inverted ≤ 2 · normal
    intro s _
    show Tinverted T0 ΔT R0 L s ≤ 2 * Tnormal T0 ΔT R0 L s
    simp only [Tnormal, Tinverted]
    nlinarith [logistic_lt_one ((s - R0) / L), logistic_pos (-(s - R0) / L)]
  · intro s _
    simpa [A, normalAtm] using hxs

end Atmosphere

end ExoLean
