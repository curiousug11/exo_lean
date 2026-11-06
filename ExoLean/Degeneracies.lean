import ExoLean.Identifiability

/-!
# Constructive degeneracies of the analytic operator under opacity-regime assumptions

* `Iso.grey_temperature_unidentifiable`: **flat-spectrum (grey) degeneracy.** If every opacity
  source is grey on the observed band, then *every* temperature `T' > 0` reproduces the
  spectrum exactly (after re-tuning `P0`). The scale height, and hence `T`, is completely
  unconstrained.
* `Iso.lecavelier_slope`: **Lecavelier des Etangs et al. (2008).** For power-law opacities
  `σᵢ ∝ λ^β`, `dR_p / d ln λ = β H` exactly.
* `Iso.powerLaw_slope_degeneracy`: if the slope `β` is a free parameter (as in power-law
  haze parameterisations), then `(T, β) ↦ (cT, β/c)` reproduces the spectrum exactly.
  Only the product `β H` is constrained (`Iso.slopeProduct_identifiable`).
-/

noncomputable section

open Real

set_option linter.unusedSectionVars false

namespace ExoLean

namespace Iso

variable {ι : Type*} [Fintype ι] {p : Iso ι}

/-! ### Grey opacities -/

/-- **Grey-cloud / flat-spectrum degeneracy.** If every cross-section is grey on the band `S`,
then for every `T' > 0` there is a reference pressure `P0' > 0` such that the atmosphere at
temperature `T'` has exactly the same spectrum on `S`. -/
theorem grey_temperature_unidentifiable (hp : p.Valid) {σ : ι → ℝ → ℝ} {S : Set ℝ}
    (hgrey : ∀ i, GreyOn (σ i) S) (hκ : ∀ w ∈ S, 0 < p.opacity σ w) {T' : ℝ} (hT' : 0 < T') :
    ∃ P0', 0 < P0' ∧ ∀ w ∈ S,
      ({ p with T := T', P0 := P0' } : Iso ι).transitRadius σ w = p.transitRadius σ w := by
  choose c hc using hgrey
  set κ0 := ∑ i, p.absCoeff i * c i + p.κc
  have hκ0 : ∀ w ∈ S, p.opacity σ w = κ0 := fun w hw => by
    simp only [opacity, κ0]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hc i w hw]
  set p' : Iso ι := { p with T := T' }
  have hp' : p'.Valid := ⟨hT', hp.m_pos, hp.g_pos, hp.R0_pos, hp.P0_pos, hp.X_nonneg, hp.κc_nonneg⟩
  obtain ⟨P0', hP0', hL⟩ := exists_P0_level hp' (p.level + p.H * log κ0 - p'.H * log κ0)
  refine ⟨P0', hP0', fun w hw => ?_⟩
  set q : Iso ι := { p' with P0 := P0' }
  have hq : q.Valid := ⟨hT', hp.m_pos, hp.g_pos, hp.R0_pos, hP0', hp.X_nonneg, hp.κc_nonneg⟩
  have hOq : q.opacity σ w = p.opacity σ w := rfl
  show q.transitRadius σ w = p.transitRadius σ w
  rw [transitRadius_eq hq (hOq ▸ hκ w hw), transitRadius_eq hp (hκ w hw), hOq, hκ0 w hw, hL]
  have : q.H = p'.H := rfl
  rw [this]
  ring

/-! ### Power-law opacities (Lecavelier des Etangs et al. 2008) -/

/-- For cloud-free power-law opacities `σᵢ(λ) = Kᵢ λ^β`,
`R_p(λ) = L + H ln C + β H ln λ` with `C = Σᵢ aᵢ Kᵢ`. -/
theorem transitRadius_powerLaw (hp : p.Valid) (hκc : p.κc = 0) {K : ι → ℝ} {β : ℝ}
    (hC : 0 < ∑ i, p.absCoeff i * K i) {w : ℝ} (hw : 0 < w) :
    p.transitRadius (fun i w => K i * w ^ β) w =
      p.level + p.H * log (∑ i, p.absCoeff i * K i) + β * p.H * log w := by
  have hO : p.opacity (fun i w => K i * w ^ β) w = (∑ i, p.absCoeff i * K i) * w ^ β := by
    simp only [opacity, hκc, add_zero, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpos : 0 < p.opacity (fun i w => K i * w ^ β) w := by
    rw [hO]; exact mul_pos hC (rpow_pos_of_pos hw β)
  rw [transitRadius_eq hp hpos, hO, log_mul hC.ne' (rpow_pos_of_pos hw β).ne', log_rpow hw]
  ring

/-- **Lecavelier des Etangs et al. (2008):** `dR_p/d ln λ = β H` for power-law opacity. -/
theorem lecavelier_slope (hp : p.Valid) (hκc : p.κc = 0) {K : ι → ℝ} {β : ℝ}
    (hC : 0 < ∑ i, p.absCoeff i * K i) (x : ℝ) :
    HasDerivAt (fun x => p.transitRadius (fun i w => K i * w ^ β) (exp x)) (β * p.H) x := by
  have hfun : (fun x => p.transitRadius (fun i w => K i * w ^ β) (exp x)) =
      fun x => (p.level + p.H * log (∑ i, p.absCoeff i * K i)) + β * p.H * x := by
    funext x
    rw [transitRadius_powerLaw hp hκc hC (exp_pos x), log_exp]
  rw [hfun]
  simpa using ((hasDerivAt_id' x).const_mul (β * p.H)).const_add
    (p.level + p.H * log (∑ i, p.absCoeff i * K i))

/-- **Slope–temperature degeneracy for free-slope power laws.** If the opacity slope is a free
parameter, then the atmosphere at temperature `c T` with slope `β/c` reproduces the spectrum of
the atmosphere at `T` with slope `β` exactly, after re-tuning `P0`. -/
theorem powerLaw_slope_degeneracy (hp : p.Valid) (hκc : p.κc = 0) {K : ι → ℝ} {β c : ℝ}
    (hc : 0 < c) (hC : 0 < ∑ i, p.absCoeff i * K i) :
    ∃ P0', 0 < P0' ∧ ∀ w, 0 < w →
      ({ p with T := c * p.T, P0 := P0' } : Iso ι).transitRadius (fun i w => K i * w ^ (β / c)) w
        = p.transitRadius (fun i w => K i * w ^ β) w := by
  set p' : Iso ι := { p with T := c * p.T }
  have hp' : p'.Valid :=
    ⟨mul_pos hc hp.T_pos, hp.m_pos, hp.g_pos, hp.R0_pos, hp.P0_pos, hp.X_nonneg, hp.κc_nonneg⟩
  have hH' : p'.H = c * p.H := by simp only [p', H]; ring
  set C := ∑ i, p.absCoeff i * K i
  obtain ⟨P0', hP0', hL⟩ := exists_P0_level hp' (p.level + p.H * log C - p'.H * log C)
  refine ⟨P0', hP0', fun w hw => ?_⟩
  set q : Iso ι := { p' with P0 := P0' }
  have hq : q.Valid := ⟨hp'.T_pos, hp.m_pos, hp.g_pos, hp.R0_pos, hP0', hp.X_nonneg, hp.κc_nonneg⟩
  have hCq : ∑ i, q.absCoeff i * K i = C := rfl
  show q.transitRadius _ w = _
  rw [transitRadius_powerLaw hq hκc (hCq ▸ hC) hw, transitRadius_powerLaw hp hκc hC hw, hCq, hL,
    show q.H = p'.H from rfl, hH']
  field_simp
  ring

/-- Conversely, within power-law models only the product `β H` (and the offset) is
identifiable. Two spectra that agree at two distinct wavelengths have equal `β H`. -/
theorem slopeProduct_identifiable {q : Iso ι} (hp : p.Valid) (hq : q.Valid)
    (hκp : p.κc = 0) (hκq : q.κc = 0) {K K' : ι → ℝ} {β β' : ℝ}
    (hC : 0 < ∑ i, p.absCoeff i * K i) (hC' : 0 < ∑ i, q.absCoeff i * K' i)
    {w1 w2 : ℝ} (hw1 : 0 < w1) (hw2 : 0 < w2) (hne : w1 ≠ w2)
    (h1 : p.transitRadius (fun i w => K i * w ^ β) w1 =
      q.transitRadius (fun i w => K' i * w ^ β') w1)
    (h2 : p.transitRadius (fun i w => K i * w ^ β) w2 =
      q.transitRadius (fun i w => K' i * w ^ β') w2) :
    β * p.H = β' * q.H := by
  rw [transitRadius_powerLaw hp hκp hC hw1, transitRadius_powerLaw hq hκq hC' hw1] at h1
  rw [transitRadius_powerLaw hp hκp hC hw2, transitRadius_powerLaw hq hκq hC' hw2] at h2
  have hlog : log w1 - log w2 ≠ 0 := by
    intro h
    exact hne (log_injOn_pos hw1 hw2 (by linarith))
  have : (β * p.H - β' * q.H) * (log w1 - log w2) = 0 := by linear_combination h1 - h2
  have := (mul_eq_zero.mp this).resolve_right hlog
  linarith

end Iso

end ExoLean
