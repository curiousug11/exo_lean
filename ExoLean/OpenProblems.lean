import ExoLean.ProfileClosure
import ExoLean.Rigidity

/-!
# Open targets for automated provers

Each target is a precisely stated `Prop`. **None of them is asserted or proved here**, and
there is no `sorry` in this library. They are the natural next goals for an AI prover. Each
outcome is useful: a proof is an identifiability theorem, and a disproof is a constructive
degeneracy.

1. `DensityProfilesIdentifiable σ Rtop S`: does the exact spectrum on the band `S` determine
   the active-species number-density profiles on the observable column? Expected to need an
   Abel-inversion + Laplace-uniqueness argument and non-degeneracy conditions on `σ`. It is
   false for grey `σ`, where the spectrum is a single number.
   `temperature_identifiable_of_densityIdentifiable` (proved) shows that this target,
   together with a closed composition, gives identifiability of the full `T(r)` profile.
2. `GaussianBandsPowerRigid`: are Gaussian absorption bands with pairwise distinct centres
   power-rigid? By `Iso.scaleHeight_eq_of_powerRigid` (proved), a positive answer gives
   identifiability of `H` for multi-band spectra.
3. `ReferenceGaugeBrokenByE1`: does keeping the `E₁(τ₀)` term of Heng & Kitzmann (2017),
   dropped in the optically thick limit, break the exact `(R0, P0)` gauge of
   `Iso.transitRadius_referenceGauge`?
-/

noncomputable section

open Real

namespace ExoLean

namespace OpenProblems

variable {ι : Type*} [Fintype ι]

/-- **Target 1.** The exact spectrum on the band `S` determines the species number densities on
the observable column `[R0, Rtop]`. -/
def DensityProfilesIdentifiable (σ : ι → ℝ → ℝ) (Rtop : ℝ) (S : Set ℝ) : Prop :=
  ∀ A B : Atmosphere ι, A.WellPosed → B.WellPosed → A.R0 = B.R0 →
    (∀ w ∈ S, A.spectrum σ Rtop w = B.spectrum σ Rtop w) →
    ∀ i, ∀ r ∈ Set.Icc A.R0 Rtop, A.speciesDensity i r = B.speciesDensity i r

/-- **Proved conditional result.** If target 1 holds for `σ`, then for atmospheres with a closed
composition (no transparent filler) and shared `R0, P0, g, m`, the spectrum determines the
full temperature profile on the observable column. -/
theorem temperature_identifiable_of_densityIdentifiable {σ : ι → ℝ → ℝ} {Rtop : ℝ}
    {S : Set ℝ} (hID : DensityProfilesIdentifiable σ Rtop S) {A B : Atmosphere ι}
    (hA : A.WellPosed) (hB : B.WellPosed)
    (hR0 : A.R0 = B.R0) (hP0 : A.P0 = B.P0) (hg : A.g = B.g) (hm : A.m = B.m)
    (hXA : ∀ r ∈ Set.Icc A.R0 Rtop, ∑ i, A.X i r = 1)
    (hXB : ∀ r ∈ Set.Icc A.R0 Rtop, ∑ i, B.X i r = 1)
    (hspec : ∀ w ∈ S, A.spectrum σ Rtop w = B.spectrum σ Rtop w) :
    ∀ r ∈ Set.Icc A.R0 Rtop, A.T r = B.T r :=
  Atmosphere.T_eq_of_speciesDensity_eq hA hB hR0 hP0 hg hm hXA hXB
    (hID A B hA hB hR0 hspec)

/-- Gaussian absorption bands `σᵢ(λ) = exp(-((λ - cᵢ)/sᵢ)²)`. -/
def gaussianBands (c s : ι → ℝ) : ι → ℝ → ℝ := fun i w => exp (-((w - c i) / s i) ^ 2)

/-- **Target 2.** Gaussian bands with pairwise distinct centres and positive widths are
power-rigid on every nonempty open band. -/
def GaussianBandsPowerRigid : Prop :=
  ∀ (c s : ι → ℝ), Function.Injective c → (∀ i, 0 < s i) →
    ∀ l u : ℝ, l < u → PowerRigid (gaussianBands c s) (Set.Ioo l u)

/-- The exponential integral `E₁(τ) = ∫₁^∞ e^{-τ t}/t dt`. -/
def expIntegralE1 (τ : ℝ) : ℝ := ∫ t in Set.Ioi (1 : ℝ), exp (-τ * t) / t

/-- Heng & Kitzmann (2017) transit radius **with** the `E₁(τ₀)` term:
`R = R0 + H [γ + E₁(τ₀) + ln τ₀]`, `τ₀ = P0 κ/g · √(2π R0/H)`. -/
def transitRadiusE1 (p : Iso ι) (σ : ι → ℝ → ℝ) (w : ℝ) : ℝ :=
  let τ0 := p.P0 * p.opacity σ w / p.g * √(2 * π * p.R0 / p.H)
  p.R0 + p.H * (γE + expIntegralE1 τ0 + log τ0)

/-- **Target 3.** The `E₁` term breaks the reference gauge: some admissible model and some
`R0' > 0` give a different spectrum after the gauge transformation of
`Iso.transitRadius_referenceGauge`. -/
def ReferenceGaugeBrokenByE1 : Prop :=
  ∃ (p : Iso ι) (σ : ι → ℝ → ℝ) (w R0' : ℝ), p.Valid ∧ 0 < R0' ∧
    transitRadiusE1 ({ p with R0 := R0', P0 := p.P0 * √(p.R0 / R0') * exp ((p.R0 - R0') / p.H) } : Iso ι) σ w ≠
      transitRadiusE1 p σ w

end OpenProblems

end ExoLean
