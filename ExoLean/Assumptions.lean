import ExoLean.Atmosphere

/-!
# The explicit assumption lattice

Classical analytic transmission-spectrum formulas (Lecavelier des Etangs et al. 2008;
Heng & Kitzmann 2017) rest on a stack of simplifying assumptions. We make each one an
explicit object so that every theorem in this library states *exactly* which ones it needs.

There are two kinds of assumptions.

* **Structural** assumptions are built into the definition of a forward model; they are
  listed in `Assumption` and documented per model.
* **Regime** assumptions are hypotheses (`Prop`s) that theorems take as arguments:
  `Atmosphere.Isothermal`, `Atmosphere.Isochemical`, `GreyOn`, `PowerLaw`.

The lattice is ordered by implication: dropping assumptions moves *up* the lattice towards
more general (less identifiable) models. The theorem
`Atmosphere.speciesDensity_of_isothermal_isochemical` is the bridge between the exact layer
(top) and the analytic layer (bottom): it shows that isothermal + isochemical + constant `g`
atmospheres have exponential number-density profiles with the scale height
`H = k_B T / (m g)`, which is the input to the analytic formulas.

| Assumption              | Exact layer (`Atmosphere`) | Analytic layer (`Iso`) |
|-------------------------|----------------------------|------------------------|
| constant gravity        | structural                 | structural             |
| constant mean mass      | structural                 | structural             |
| T,P-independent σ       | structural                 | structural             |
| transparent filler gas  | structural                 | structural             |
| no refraction           | structural                 | structural             |
| isothermal              | **not assumed**            | structural             |
| isochemical             | **not assumed**            | structural             |
| optically thick limit (`E₁(τ₀) → 0`) | not needed    | structural             |
| grey / power-law opacity| hypothesis                 | hypothesis             |
-/

noncomputable section

open Real

namespace ExoLean

/-- Catalogue of the assumptions appearing in analytic retrieval theory. -/
inductive Assumption
  | isothermal
  | isochemical
  | constantGravity
  | constantMeanMass
  | tpIndependentOpacity
  | transparentFiller
  | noRefraction
  | opticallyThickLimit
  | greyOpacity
  | powerLawOpacity
  deriving DecidableEq, Repr

/-- Structural assumptions of the exact forward model `Atmosphere.spectrum`. -/
def exactModelAssumptions : List Assumption :=
  [.constantGravity, .constantMeanMass, .tpIndependentOpacity, .transparentFiller, .noRefraction]

/-- Structural assumptions of the analytic forward model `Iso.transitRadius`. -/
def analyticModelAssumptions : List Assumption :=
  exactModelAssumptions ++ [.isothermal, .isochemical, .opticallyThickLimit]

/-- The opacity shape `φ` is grey (wavelength-independent) on the observed band `S`. -/
def GreyOn (φ : ℝ → ℝ) (S : Set ℝ) : Prop := ∃ c, ∀ w ∈ S, φ w = c

/-- The opacity shape is a power law `φ(λ) = K λ^β` on `λ > 0` (Lecavelier des Etangs 2008). -/
def PowerLaw (φ : ℝ → ℝ) (β : ℝ) : Prop := ∃ K, 0 < K ∧ ∀ w, 0 < w → φ w = K * w ^ β

namespace Atmosphere

variable {ι : Type*} (A : Atmosphere ι)

/-- Regime assumption: isothermal temperature profile. -/
def Isothermal : Prop := ∃ T0, ∀ r, A.T r = T0

/-- Regime assumption: isochemical (vertically constant) mixing ratios. -/
def Isochemical : Prop := ∀ i, ∃ x, ∀ r, A.X i r = x

variable {A}

/-- In an isothermal atmosphere the hydrostatic pressure is exponential with
scale height `H = k_B T0 / (m g)`. -/
theorem pressure_of_isothermal {T0 : ℝ} (hT : ∀ r, A.T r = T0) (r : ℝ) :
    A.pressure r = A.P0 * exp (-(r - A.R0) / (kB * T0 / (A.m * A.g))) := by
  simp only [pressure, invScaleHeight, hT, intervalIntegral.integral_const, smul_eq_mul]
  congr 2
  rw [div_div_eq_mul_div]
  ring

/-- **Bridge lemma (exact layer → analytic layer).** Under the isothermal and isochemical
regime assumptions, every species has an exponential number-density profile
`nᵢ(r) = Xᵢ P0/(k_B T0) · exp(-(r - R0)/H)` with `H = k_B T0/(m g)`. -/
theorem speciesDensity_of_isothermal_isochemical {T0 : ℝ} (hT : ∀ r, A.T r = T0)
    {x : ι → ℝ} (hX : ∀ i r, A.X i r = x i) (i : ι) (r : ℝ) :
    A.speciesDensity i r =
      x i * A.P0 / (kB * T0) * exp (-(r - A.R0) / (kB * T0 / (A.m * A.g))) := by
  rw [speciesDensity, numberDensity, pressure_of_isothermal hT, hX, hT]
  ring

end Atmosphere

end ExoLean
