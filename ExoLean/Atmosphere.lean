import ExoLean.Basic

/-!
# The exact (non-analytic) forward model

A spherically symmetric atmosphere above a reference radius `R0` is described by

* a temperature profile `T : ℝ → ℝ` (radius ↦ temperature), **arbitrary**: no isothermal
  assumption is made in this file;
* volume-mixing-ratio profiles `X i : ℝ → ℝ` for spectrally active species `i : ι`,
  **arbitrary**: no isochemical assumption is made;
* reference pressure `P0 = P(R0)`, constant gravity `g` and mean particle mass `m`.

The pressure is *defined* as the solution of hydrostatic equilibrium
`dP/dr = -ρ g`, `ρ = m P / (k_B T)`, i.e.
`P(r) = P0 · exp (-∫_{R0}^{r} m g / (k_B T(s)) ds)`, and we *prove* it satisfies the ODE
(`Atmosphere.hasDerivAt_pressure`).

The transit radius is the exact geometric (no refraction) chord integral
```
τ(b, λ)  = 2 ∫_b^{R_top} α(r, λ) r / √(r² − b²) dr
R_p(λ)²  = R0² + 2 ∫_{R0}^{R_top} b (1 − e^{−τ(b, λ)}) db
```
with the extinction coefficient `α(r, λ) = Σᵢ σᵢ(λ) nᵢ(r)`.

## Assumptions baked into this layer (see `ExoLean.Assumptions`)

* constant gravity `g` and constant mean particle mass `m` (trace absorbers);
* cross-sections `σᵢ(λ)` independent of `T` and `P`;
* the remaining gas (`1 − Σᵢ Xᵢ`) is a spectrally inactive filler;
* the region `r < R0` is opaque; the atmosphere is truncated at `R_top`; no refraction.
-/

noncomputable section

open Real intervalIntegral

namespace ExoLean

/-- A spherically symmetric atmosphere with active species indexed by `ι`. -/
structure Atmosphere (ι : Type*) where
  /-- reference (opaque-surface) radius -/
  R0 : ℝ
  /-- pressure at `R0` -/
  P0 : ℝ
  /-- (constant) gravitational acceleration -/
  g : ℝ
  /-- mean particle mass (kg), i.e. `μ m_u` -/
  m : ℝ
  /-- temperature profile, as a function of radius -/
  T : ℝ → ℝ
  /-- volume-mixing-ratio profiles of the active species, as functions of radius -/
  X : ι → ℝ → ℝ

namespace Atmosphere

variable {ι : Type*} (A : Atmosphere ι)

/-- Local inverse scale height `1/H(r) = m g / (k_B T(r))`. -/
def invScaleHeight (r : ℝ) : ℝ := A.m * A.g / (kB * A.T r)

/-- Hydrostatic pressure profile `P(r) = P0 exp(-∫_{R0}^r m g /(k_B T))`. -/
def pressure (r : ℝ) : ℝ := A.P0 * exp (-∫ s in A.R0..r, A.invScaleHeight s)

/-- Total number density `n = P / (k_B T)` (ideal gas). -/
def numberDensity (r : ℝ) : ℝ := A.pressure r / (kB * A.T r)

/-- Mass density `ρ = m n`. -/
def massDensity (r : ℝ) : ℝ := A.m * A.numberDensity r

/-- Number density of species `i`: `nᵢ = Xᵢ n`. -/
def speciesDensity (i : ι) (r : ℝ) : ℝ := A.X i r * A.numberDensity r

/-- Regularity/positivity hypotheses making the atmosphere physically meaningful. -/
structure WellPosed : Prop where
  P0_pos : 0 < A.P0
  g_pos : 0 < A.g
  m_pos : 0 < A.m
  T_pos : ∀ r, 0 < A.T r
  T_cont : Continuous A.T

/-- Physically admissible mixing ratios above the reference radius:
nonnegative, and summing to at most one (the remainder is the inactive filler gas). -/
def PhysicalVMR [Fintype ι] : Prop :=
  ∀ r, A.R0 ≤ r → (∀ i, 0 ≤ A.X i r) ∧ ∑ i, A.X i r ≤ 1

variable {A}

theorem WellPosed.continuous_invScaleHeight (h : A.WellPosed) :
    Continuous A.invScaleHeight :=
  continuous_const.div (continuous_const.mul h.T_cont)
    (fun r => (mul_pos kB_pos (h.T_pos r)).ne')

theorem WellPosed.invScaleHeight_pos (h : A.WellPosed) (r : ℝ) : 0 < A.invScaleHeight r :=
  div_pos (mul_pos h.m_pos h.g_pos) (mul_pos kB_pos (h.T_pos r))

theorem WellPosed.pressure_pos (h : A.WellPosed) (r : ℝ) : 0 < A.pressure r :=
  mul_pos h.P0_pos (exp_pos _)

theorem WellPosed.numberDensity_pos (h : A.WellPosed) (r : ℝ) : 0 < A.numberDensity r :=
  div_pos (h.pressure_pos r) (mul_pos kB_pos (h.T_pos r))

theorem pressure_R0 : A.pressure A.R0 = A.P0 := by
  simp [pressure]

/-- **Hydrostatic equilibrium.** The pressure profile solves `dP/dr = -ρ(r) g`. -/
theorem WellPosed.hasDerivAt_pressure (h : A.WellPosed) (r : ℝ) :
    HasDerivAt A.pressure (-(A.massDensity r * A.g)) r := by
  have hI : HasDerivAt (fun u => ∫ s in A.R0..u, A.invScaleHeight s)
      (A.invScaleHeight r) r :=
    (h.continuous_invScaleHeight.integral_hasStrictDerivAt A.R0 r).hasDerivAt
  have hP : HasDerivAt (fun u => A.P0 * exp (-∫ s in A.R0..u, A.invScaleHeight s))
      (A.P0 * (exp (-∫ s in A.R0..r, A.invScaleHeight s) * -A.invScaleHeight r)) r :=
    (hI.neg.exp).const_mul A.P0
  have e : -(A.massDensity r * A.g) =
      A.P0 * (exp (-∫ s in A.R0..r, A.invScaleHeight s) * -A.invScaleHeight r) := by
    simp only [massDensity, numberDensity, pressure, invScaleHeight]
    ring
  rw [e]
  exact hP

/-! ### Exact forward operator -/

/-- Extinction coefficient `α(r, λ) = Σᵢ σᵢ(λ) nᵢ(r)` (cross-sections independent of `T`,`P`;
the filler gas is transparent). -/
def extinction [Fintype ι] (σ : ι → ℝ → ℝ) (A : Atmosphere ι) (r w : ℝ) : ℝ :=
  ∑ i, σ i w * A.speciesDensity i r

end Atmosphere

/-- Slant (chord) optical depth at impact parameter `b` through an atmosphere with
extinction profile `α`, truncated at `Rtop`. -/
def slantOpticalDepth (α : ℝ → ℝ) (Rtop b : ℝ) : ℝ :=
  2 * ∫ r in b..Rtop, α r * r / √(r ^ 2 - b ^ 2)

/-- Exact geometric transit radius at wavelength `w`, for an opaque core of radius `Rs`
and an extinction field `α(r, w)`:
`R_p² = Rs² + 2 ∫_{Rs}^{Rtop} b (1 - exp(-τ(b, w))) db`. -/
def transitRadius (Rs Rtop : ℝ) (α : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  √(Rs ^ 2 + 2 * ∫ b in Rs..Rtop, b * (1 - exp (-slantOpticalDepth (fun r => α r w) Rtop b)))

namespace Atmosphere

variable {ι : Type*} [Fintype ι]

/-- **The exact forward operator** `F : Θ → (λ ↦ R_p(λ))`. -/
def spectrum (σ : ι → ℝ → ℝ) (Rtop : ℝ) (A : Atmosphere ι) : ℝ → ℝ :=
  transitRadius A.R0 Rtop (A.extinction σ)

/-- **Factorisation lemma.** The exact spectrum depends on the atmosphere *only* through
the reference radius and the number-density profiles of the active species. In particular
it does not see `T(r)`, `X(r)`, `P(r)`, `g` or `m` separately. -/
theorem spectrum_eq_of_speciesDensity_eq {A B : Atmosphere ι} (hR : A.R0 = B.R0)
    (hn : ∀ i r, A.speciesDensity i r = B.speciesDensity i r)
    (σ : ι → ℝ → ℝ) (Rtop : ℝ) : A.spectrum σ Rtop = B.spectrum σ Rtop := by
  have : A.extinction σ = B.extinction σ := by
    funext r w; simp [extinction, hn]
  simp [spectrum, hR, this]

end Atmosphere

end ExoLean
