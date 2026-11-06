import ExoLean.Assumptions

/-!
# The analytic isothermal forward operator (Heng & Kitzmann 2017)

In the isothermal, isochemical, constant-`g` regime, and in the optically thick limit
(`E₁(τ₀) → 0`), the transit radius is
```
R_p(λ) = R0 + H [ γ + ln( P0 κ(λ)/g · √(2π R0 / H) ) ],     H = k_B T / (m g),
κ(λ)   = Σᵢ (Xᵢ / m) σᵢ(λ) + κ_cloud,
```
with `σᵢ` the absorber cross-sections and `κ_cloud` a grey cloud mass opacity
(Heng & Kitzmann 2017; Lecavelier des Etangs et al. 2008). Here the formula is the
*definition* of the analytic forward operator `Iso.transitRadius`. Its derivation from the
exact chord integral in `ExoLean.Atmosphere` is not formalised.

The key structural identity is `Iso.transitRadius_eq`:
```
R_p(λ) = L(θ) + H · ln κ(λ),      L(θ) = R0 + H [γ + ln(P0/g · √(2π R0/H))],
```
so the parameters enter only through `H`, the "level" `L`, and the opacity function.

This file proves the exact symmetries (gauge transformations) of the operator:

* `Iso.transitRadius_referenceGauge`: the (R0, P0) reference radius/pressure degeneracy;
* `Iso.transitRadius_normalization`: the (P0, Xᵢ, κ_cloud) normalisation degeneracy
  (Benneke & Seager 2012; Heng & Kitzmann 2017);
* `Iso.transitRadius_T_g`: the temperature–gravity degeneracy (only `T/g` appears);
* `Iso.transitRadius_T_m`: the temperature–mean-molecular-mass degeneracy.
-/

noncomputable section

open Real

set_option linter.unusedSectionVars false

namespace ExoLean

/-- Parameters `θ = (T, m, g, R0, P0, X, κ_cloud)` of the isothermal analytic model. -/
structure Iso (ι : Type*) where
  T : ℝ
  m : ℝ
  g : ℝ
  R0 : ℝ
  P0 : ℝ
  X : ι → ℝ
  κc : ℝ

namespace Iso

variable {ι : Type*} [Fintype ι] (p : Iso ι)

/-- Pressure scale height `H = k_B T / (m g)`. -/
def H : ℝ := kB * p.T / (p.m * p.g)

/-- Absorber mass-opacity coefficient `aᵢ = Xᵢ / m`, so `κ = Σᵢ aᵢ σᵢ + κ_cloud`. -/
def absCoeff (i : ι) : ℝ := p.X i / p.m

/-- Total mass opacity `κ(λ) = Σᵢ (Xᵢ/m) σᵢ(λ) + κ_cloud`. -/
def opacity (σ : ι → ℝ → ℝ) (w : ℝ) : ℝ := ∑ i, p.absCoeff i * σ i w + p.κc

/-- The "level" `L(θ) = R0 + H [γ + ln(P0/g · √(2π R0/H))]`. -/
def level : ℝ := p.R0 + p.H * (γE + log (p.P0 / p.g * √(2 * π * p.R0 / p.H)))

/-- **Analytic forward operator** (Heng & Kitzmann 2017, optically thick limit). -/
def transitRadius (σ : ι → ℝ → ℝ) (w : ℝ) : ℝ :=
  p.R0 + p.H * (γE + log (p.P0 * p.opacity σ w / p.g * √(2 * π * p.R0 / p.H)))

/-- Physical admissibility of the parameters. -/
structure Valid : Prop where
  T_pos : 0 < p.T
  m_pos : 0 < p.m
  g_pos : 0 < p.g
  R0_pos : 0 < p.R0
  P0_pos : 0 < p.P0
  X_nonneg : ∀ i, 0 ≤ p.X i
  κc_nonneg : 0 ≤ p.κc

variable {p}

theorem Valid.H_pos (hp : p.Valid) : 0 < p.H :=
  div_pos (mul_pos kB_pos hp.T_pos) (mul_pos hp.m_pos hp.g_pos)

theorem Valid.absCoeff_nonneg (hp : p.Valid) (i : ι) : 0 ≤ p.absCoeff i :=
  div_nonneg (hp.X_nonneg i) hp.m_pos.le

theorem Valid.sqrt_pos (hp : p.Valid) : 0 < √(2 * π * p.R0 / p.H) :=
  Real.sqrt_pos.mpr (div_pos (mul_pos (mul_pos two_pos pi_pos) hp.R0_pos) hp.H_pos)

/-- **Structural identity:** `R_p(λ) = L(θ) + H ln κ(λ)`. -/
theorem transitRadius_eq (hp : p.Valid) {σ : ι → ℝ → ℝ} {w : ℝ} (hκ : 0 < p.opacity σ w) :
    p.transitRadius σ w = p.level + p.H * log (p.opacity σ w) := by
  have h1 : 0 < p.P0 / p.g * √(2 * π * p.R0 / p.H) := mul_pos (div_pos hp.P0_pos hp.g_pos) hp.sqrt_pos
  have : p.P0 * p.opacity σ w / p.g * √(2 * π * p.R0 / p.H) =
      (p.P0 / p.g * √(2 * π * p.R0 / p.H)) * p.opacity σ w := by ring
  rw [transitRadius, level, this, log_mul h1.ne' hκ.ne']
  ring

/-- Two parameter sets with the same `H`, the same level and the same opacity give the same
spectrum. -/
theorem transitRadius_eq_of {q : Iso ι} (hp : p.Valid) (hq : q.Valid) {σ : ι → ℝ → ℝ} {w : ℝ}
    (hκ : 0 < p.opacity σ w) (hH : p.H = q.H) (hL : p.level = q.level)
    (hO : p.opacity σ w = q.opacity σ w) :
    p.transitRadius σ w = q.transitRadius σ w := by
  rw [transitRadius_eq hp hκ, transitRadius_eq hq (hO ▸ hκ), hH, hL, hO]

/-! ### Level matching -/

/-- Any target level can be reached by tuning the reference pressure alone. This is the
engine behind every degeneracy below. -/
theorem exists_P0_level (hp : p.Valid) (L : ℝ) :
    ∃ P0' : ℝ, 0 < P0' ∧ ({ p with P0 := P0' } : Iso ι).level = L := by
  set s := √(2 * π * p.R0 / p.H)
  have hs : 0 < s := hp.sqrt_pos
  refine ⟨p.g / s * exp ((L - p.R0) / p.H - γE), by
    have := hp.g_pos; positivity, ?_⟩
  have hH := hp.H_pos
  show p.R0 + p.H * (γE + log (p.g / s * exp ((L - p.R0) / p.H - γE) / p.g * s)) = L
  have : p.g / s * exp ((L - p.R0) / p.H - γE) / p.g * s = exp ((L - p.R0) / p.H - γE) := by
    field_simp [hp.g_pos.ne']
  rw [this, log_exp]
  field_simp
  ring

/-! ### Exact gauge symmetries of the analytic operator -/

/-- **The (R0, P0) reference gauge.** For every `R0' > 0`, moving the reference radius to
`R0'` and the reference pressure to `P0' = P0 √(R0/R0') exp((R0 − R0')/H)` leaves the
spectrum exactly unchanged at every wavelength. The `√R0` factor of the Heng–Kitzmann
formula is compensated exactly by the `√(R0/R0')` term. -/
theorem transitRadius_referenceGauge (hp : p.Valid) {R0' : ℝ} (hR0' : 0 < R0')
    (σ : ι → ℝ → ℝ) (w : ℝ) (hκ : 0 < p.opacity σ w) :
    ({ p with R0 := R0', P0 := p.P0 * √(p.R0 / R0') * exp ((p.R0 - R0') / p.H) } : Iso ι).transitRadius σ w =
      p.transitRadius σ w := by
  set q : Iso ι := { p with R0 := R0', P0 := p.P0 * √(p.R0 / R0') * exp ((p.R0 - R0') / p.H) }
  have hq : q.Valid :=
    ⟨hp.T_pos, hp.m_pos, hp.g_pos, hR0', by have := hp.P0_pos; have := hp.R0_pos; positivity,
      hp.X_nonneg, hp.κc_nonneg⟩
  have hHq : q.H = p.H := rfl
  have hO : q.opacity σ w = p.opacity σ w := rfl
  refine transitRadius_eq_of hq hp (hO ▸ hκ) hHq ?_ hO
  have hH := hp.H_pos
  have hR := hp.R0_pos
  have hsq : √(p.R0 / R0') * √(2 * π * R0' / p.H) = √(2 * π * p.R0 / p.H) := by
    rw [← sqrt_mul (div_pos hR hR0').le]
    congr 1
    field_simp
  have harg : q.P0 / q.g * √(2 * π * q.R0 / q.H) =
      (p.P0 / p.g * √(2 * π * p.R0 / p.H)) * exp ((p.R0 - R0') / p.H) := by
    show p.P0 * √(p.R0 / R0') * exp ((p.R0 - R0') / p.H) / p.g * √(2 * π * R0' / p.H) = _
    rw [← hsq]
    ring
  have hpos : 0 < p.P0 / p.g * √(2 * π * p.R0 / p.H) :=
    mul_pos (div_pos hp.P0_pos hp.g_pos) hp.sqrt_pos
  rw [level, level, harg, hHq, log_mul hpos.ne' (exp_pos _).ne', log_exp]
  show R0' + p.H * (γE + (log (p.P0 / p.g * √(2 * π * p.R0 / p.H)) + (p.R0 - R0') / p.H)) =
    p.R0 + p.H * (γE + log (p.P0 / p.g * √(2 * π * p.R0 / p.H)))
  field_simp
  ring

/-- **Normalisation degeneracy.** Scaling every abundance and the cloud opacity by `c > 0` and
the reference pressure by `1/c` leaves the spectrum exactly unchanged. -/
theorem transitRadius_normalization {c : ℝ} (hc : 0 < c) (σ : ι → ℝ → ℝ) (w : ℝ) :
    ({ p with P0 := p.P0 / c, X := fun i => c * p.X i, κc := c * p.κc } : Iso ι).transitRadius σ w =
      p.transitRadius σ w := by
  have hO : ({ p with P0 := p.P0 / c, X := fun i => c * p.X i, κc := c * p.κc } : Iso ι).opacity σ w
      = c * p.opacity σ w := by
    simp only [opacity, absCoeff, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  simp only [transitRadius, H] at hO ⊢
  have h : p.P0 / c * (c * p.opacity σ w) = p.P0 * p.opacity σ w := by field_simp
  rw [hO, h]

/-- **Temperature–gravity degeneracy.** `(T, g, P0) ↦ (cT, cg, cP0)` leaves the spectrum
exactly unchanged: the spectrum constrains `T/g`, not `T` and `g` separately. -/
theorem transitRadius_T_g {c : ℝ} (hc : 0 < c) (σ : ι → ℝ → ℝ) (w : ℝ) :
    ({ p with T := c * p.T, g := c * p.g, P0 := c * p.P0 } : Iso ι).transitRadius σ w =
      p.transitRadius σ w := by
  simp only [transitRadius, H, opacity, absCoeff]
  have h1 : kB * (c * p.T) / (p.m * (c * p.g)) = kB * p.T / (p.m * p.g) := by
    rw [show p.m * (c * p.g) = c * (p.m * p.g) by ring, show kB * (c * p.T) = c * (kB * p.T) by ring,
      mul_div_mul_left _ _ hc.ne']
  have h2 : c * p.P0 * (∑ i, p.X i / p.m * σ i w + p.κc) / (c * p.g) =
      p.P0 * (∑ i, p.X i / p.m * σ i w + p.κc) / p.g := by
    rw [mul_assoc, mul_div_mul_left _ _ hc.ne']
  rw [h1, h2]

/-- **Temperature–mean-molecular-mass degeneracy.** `(T, m, X) ↦ (cT, cm, cX)` leaves the
spectrum exactly unchanged (the opacity per unit mass `X/m` is preserved). -/
theorem transitRadius_T_m {c : ℝ} (hc : 0 < c) (σ : ι → ℝ → ℝ) (w : ℝ) :
    ({ p with T := c * p.T, m := c * p.m, X := fun i => c * p.X i } : Iso ι).transitRadius σ w =
      p.transitRadius σ w := by
  simp only [transitRadius, H, opacity, absCoeff]
  have h1 : kB * (c * p.T) / (c * p.m * p.g) = kB * p.T / (p.m * p.g) := by
    rw [show c * p.m * p.g = c * (p.m * p.g) by ring, show kB * (c * p.T) = c * (kB * p.T) by ring,
      mul_div_mul_left _ _ hc.ne']
  have h2 : ∀ i, c * p.X i / (c * p.m) = p.X i / p.m := fun i => mul_div_mul_left _ _ hc.ne'
  simp only [h1, h2]

end Iso

end ExoLean
