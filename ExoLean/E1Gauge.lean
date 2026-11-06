import ExoLean.OpenProblems

/-!
# Target 3 resolved: the `E₁(τ₀)` term breaks the reference gauge

In the optically thick limit, `R0 + H [γ + ln τ₀]` is exactly invariant under the gauge
`(R0, P0) ↦ (R0', P0 √(R0/R0') e^{(R0−R0')/H})`, because that map sends
`τ₀ ↦ τ₀ · e^{(R0−R0')/H}` (`Iso.tau0_referenceGauge`). Keeping the `E₁(τ₀)` term of
Heng & Kitzmann (2017), the transit radius shifts by **exactly**
```
ΔR_p = H · (E₁(τ₀ e^{(R0−R0')/H}) − E₁(τ₀))         (`Iso.transitRadiusE1_referenceGauge`)
```
`E₁` is strictly decreasing on `(0, ∞)` (`expIntegralE1_strictAntiOn`), so the shift is nonzero
whenever `R0' ≠ R0`. So **every** admissible model breaks the gauge
(`Iso.transitRadiusE1_gauge_ne`), and `OpenProblems.ReferenceGaugeBrokenByE1` holds
(`referenceGaugeBrokenByE1`). Moving the reference radius outward (`R0' > R0`) strictly
*raises* the transit radius (`Iso.transitRadiusE1_gauge_lt`).

Physically: the (R0, P0) degeneracy is exact only in the `τ₀ ≫ 1` limit. Since
`E₁(τ) ≤ e^{−τ}`, the breaking is exponentially weak there, which is why it is effectively a
degeneracy in practice.
-/

noncomputable section

open Real MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ExoLean

open OpenProblems

theorem integrableOn_E1_integrand {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun t => exp (-τ * t) / t) (Ioi 1) := by
  refine (exp_neg_integrableOn_Ioi 1 hτ).mono' ?_ ?_
  · exact (ContinuousOn.div (by fun_prop) continuousOn_id
      (fun t (ht : t ∈ Ioi (1 : ℝ)) => (zero_lt_one.trans ht).ne')).aestronglyMeasurable
      measurableSet_Ioi
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 1 < t) => ?_
    rw [norm_div, Real.norm_of_nonneg (exp_pos _).le, Real.norm_of_nonneg (by linarith)]
    exact div_le_self (exp_pos _).le ht.le

/-- `E₁` is strictly decreasing on `(0, ∞)`. -/
theorem expIntegralE1_strictAntiOn : StrictAntiOn expIntegralE1 (Ioi 0) := by
  intro a (ha : 0 < a) b (hb : 0 < b) hab
  have hdiff : expIntegralE1 a - expIntegralE1 b =
      ∫ t in Ioi (1 : ℝ), (exp (-a * t) / t - exp (-b * t) / t) := by
    rw [expIntegralE1, expIntegralE1,
      integral_sub (integrableOn_E1_integrand ha) (integrableOn_E1_integrand hb)]
  have hpt : ∀ t ∈ Ioi (1 : ℝ), 0 < exp (-a * t) / t - exp (-b * t) / t := fun t ht => by
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    rw [sub_pos]
    exact div_lt_div_of_pos_right (exp_lt_exp.mpr (by nlinarith)) ht0
  have hpos : 0 < ∫ t in Ioi (1 : ℝ), (exp (-a * t) / t - exp (-b * t) / t) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hpt t ht).le)
      ((integrableOn_E1_integrand ha).sub (integrableOn_E1_integrand hb))]
    have hsub : Ioi (1 : ℝ) ⊆ Function.support
        (fun t => exp (-a * t) / t - exp (-b * t) / t) ∩ Ioi 1 :=
      fun t ht => ⟨(hpt t ht).ne', ht⟩
    exact lt_of_lt_of_le (by simp [Real.volume_Ioi]) (measure_mono hsub)
  linarith

namespace Iso

variable {ι : Type*} [Fintype ι] {p : Iso ι}

/-- The optical-depth scale `τ₀ = P0 κ/g · √(2π R0/H)`. -/
def tau0 (p : Iso ι) (σ : ι → ℝ → ℝ) (w : ℝ) : ℝ :=
  p.P0 * p.opacity σ w / p.g * √(2 * π * p.R0 / p.H)

/-- The reference-gauge transform of `p` (as in `Iso.transitRadius_referenceGauge`). -/
def gauge (p : Iso ι) (R0' : ℝ) : Iso ι :=
  { p with R0 := R0', P0 := p.P0 * √(p.R0 / R0') * exp ((p.R0 - R0') / p.H) }

theorem transitRadiusE1_eq (p : Iso ι) (σ : ι → ℝ → ℝ) (w : ℝ) :
    transitRadiusE1 p σ w = p.R0 + p.H * (γE + expIntegralE1 (p.tau0 σ w) + log (p.tau0 σ w)) :=
  rfl

theorem Valid.tau0_pos (hp : p.Valid) {σ : ι → ℝ → ℝ} {w : ℝ} (hκ : 0 < p.opacity σ w) :
    0 < p.tau0 σ w :=
  mul_pos (div_pos (mul_pos hp.P0_pos hκ) hp.g_pos) hp.sqrt_pos

/-- The gauge multiplies `τ₀` by `e^{(R0 − R0')/H}`. -/
theorem tau0_referenceGauge (hp : p.Valid) {R0' : ℝ} (hR0' : 0 < R0') (σ : ι → ℝ → ℝ)
    (w : ℝ) : (p.gauge R0').tau0 σ w = p.tau0 σ w * exp ((p.R0 - R0') / p.H) := by
  have hH := hp.H_pos
  have hR := hp.R0_pos
  have hsq : √(p.R0 / R0') * √(2 * π * R0' / p.H) = √(2 * π * p.R0 / p.H) := by
    rw [← sqrt_mul (div_pos hR hR0').le]
    congr 1
    field_simp
  show p.P0 * √(p.R0 / R0') * exp ((p.R0 - R0') / p.H) * p.opacity σ w / p.g *
    √(2 * π * R0' / p.H) = p.P0 * p.opacity σ w / p.g * √(2 * π * p.R0 / p.H) * _
  rw [← hsq]
  ring

/-- **Exact gauge shift with the `E₁` term.** -/
theorem transitRadiusE1_referenceGauge (hp : p.Valid) {R0' : ℝ} (hR0' : 0 < R0')
    (σ : ι → ℝ → ℝ) (w : ℝ) (hκ : 0 < p.opacity σ w) :
    transitRadiusE1 (p.gauge R0') σ w = transitRadiusE1 p σ w +
      p.H * (expIntegralE1 (p.tau0 σ w * exp ((p.R0 - R0') / p.H)) - expIntegralE1 (p.tau0 σ w)) := by
  have hH := hp.H_pos
  rw [transitRadiusE1_eq, transitRadiusE1_eq, tau0_referenceGauge hp hR0',
    log_mul (hp.tau0_pos hκ).ne' (exp_pos _).ne', log_exp]
  show R0' + p.H * _ = _
  field_simp
  ring

/-- **The `E₁` term breaks the reference gauge for every admissible model.** -/
theorem transitRadiusE1_gauge_ne (hp : p.Valid) {R0' : ℝ} (hR0' : 0 < R0') (hne : R0' ≠ p.R0)
    (σ : ι → ℝ → ℝ) (w : ℝ) (hκ : 0 < p.opacity σ w) :
    transitRadiusE1 (p.gauge R0') σ w ≠ transitRadiusE1 p σ w := by
  rw [transitRadiusE1_referenceGauge hp hR0' σ w hκ]
  have hτ := hp.tau0_pos hκ
  have hH := hp.H_pos
  have hexp : exp ((p.R0 - R0') / p.H) ≠ 1 := by
    rw [Ne, exp_eq_one_iff, div_eq_zero_iff, not_or]
    exact ⟨sub_ne_zero.mpr (Ne.symm hne), hH.ne'⟩
  have hτne : p.tau0 σ w * exp ((p.R0 - R0') / p.H) ≠ p.tau0 σ w := by
    intro h
    exact hexp (by
      have := congrArg (· / p.tau0 σ w) h
      simpa [hτ.ne'] using this)
  have hE : expIntegralE1 (p.tau0 σ w * exp ((p.R0 - R0') / p.H)) ≠ expIntegralE1 (p.tau0 σ w) :=
    fun h => hτne (expIntegralE1_strictAntiOn.injOn (mul_pos hτ (exp_pos _)) hτ h)
  intro h
  have : p.H * (expIntegralE1 (p.tau0 σ w * exp ((p.R0 - R0') / p.H)) -
      expIntegralE1 (p.tau0 σ w)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · exact hH.ne' h'
  · exact hE (sub_eq_zero.mp h')

/-- Moving the reference radius outward strictly raises the `E₁`-corrected transit radius. -/
theorem transitRadiusE1_gauge_lt (hp : p.Valid) {R0' : ℝ} (hlt : p.R0 < R0')
    (σ : ι → ℝ → ℝ) (w : ℝ) (hκ : 0 < p.opacity σ w) :
    transitRadiusE1 p σ w < transitRadiusE1 (p.gauge R0') σ w := by
  have hR0' : 0 < R0' := hp.R0_pos.trans hlt
  rw [transitRadiusE1_referenceGauge hp hR0' σ w hκ]
  have hτ := hp.tau0_pos hκ
  have hH := hp.H_pos
  have hsmall : p.tau0 σ w * exp ((p.R0 - R0') / p.H) < p.tau0 σ w := by
    have : exp ((p.R0 - R0') / p.H) < 1 := by
      rw [← exp_zero]
      exact exp_lt_exp.mpr (div_neg_of_neg_of_pos (by linarith) hH)
    nlinarith
  have := expIntegralE1_strictAntiOn (mul_pos hτ (exp_pos _)) hτ hsmall
  nlinarith

end Iso

/-- **Target 3 holds.** -/
theorem referenceGaugeBrokenByE1 {ι : Type*} [Fintype ι] :
    ReferenceGaugeBrokenByE1 (ι := ι) := by
  let p : Iso ι := ⟨1, 1, 1, 1, 1, fun _ => 0, 1⟩
  have hp : p.Valid := ⟨one_pos, one_pos, one_pos, one_pos, one_pos, fun _ => le_rfl, zero_le_one⟩
  have hκ : 0 < p.opacity (fun _ _ => 0) 0 := by simp [Iso.opacity, p]
  exact ⟨p, fun _ _ => 0, 0, 2, hp, two_pos,
    Iso.transitRadiusE1_gauge_ne hp two_pos (by norm_num [p]) _ _ hκ⟩

end ExoLean
