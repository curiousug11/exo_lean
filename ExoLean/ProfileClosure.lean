import ExoLean.ProfileDegeneracy

/-!
# Closing the composition removes the profile degeneracy (at the density level)

`Atmosphere.temperature_profile_unidentifiable` relies on a transparent filler gas whose
density the spectrum never sees. This file proves the converse at the level of number
densities. Suppose **every** constituent is listed (`Σᵢ Xᵢ = 1`, so nothing is
spectrally invisible), and `R0, P0, g, m` are shared. Then equal species number densities
force equal temperature profiles **everywhere**.

The proof is a uniqueness argument for hydrostatic equilibrium. Equal densities give equal
`dP/dr`. The pressure difference therefore has zero derivative and vanishes at `R0`. So the
pressures agree, and then so do the temperatures `T = P/(k_B n)`.

So, in the exact model, temperature-profile identifiability reduces to whether **the
spectrum determines the number-density profiles** (an Abel/Laplace inversion problem). That
step is stated as the open target `OpenProblems.DensityProfilesIdentifiable`.
-/

noncomputable section

open Real

namespace ExoLean

namespace Atmosphere

variable {ι : Type*} [Fintype ι] {A B : Atmosphere ι}

/-- **Closed composition ⇒ the temperature profile is determined by the species densities.**
Everything is local to the observable column `[R0, Rtop]`: if every constituent is listed
there (`Σᵢ Xᵢ = 1`) and the species number densities agree there, then the temperature
profiles agree there. -/
theorem T_eq_of_speciesDensity_eq (hA : A.WellPosed) (hB : B.WellPosed)
    (hR0 : A.R0 = B.R0) (hP0 : A.P0 = B.P0) (hg : A.g = B.g) (hm : A.m = B.m) {Rtop : ℝ}
    (hXA : ∀ r ∈ Set.Icc A.R0 Rtop, ∑ i, A.X i r = 1)
    (hXB : ∀ r ∈ Set.Icc A.R0 Rtop, ∑ i, B.X i r = 1)
    (hn : ∀ i, ∀ r ∈ Set.Icc A.R0 Rtop, A.speciesDensity i r = B.speciesDensity i r) :
    ∀ r ∈ Set.Icc A.R0 Rtop, A.T r = B.T r := by
  have hN : ∀ r ∈ Set.Icc A.R0 Rtop, A.numberDensity r = B.numberDensity r := fun r hr => by
    have eA : ∑ i, A.speciesDensity i r = A.numberDensity r := by
      simp [speciesDensity, ← Finset.sum_mul, hXA r hr]
    have eB : ∑ i, B.speciesDensity i r = B.numberDensity r := by
      simp [speciesDensity, ← Finset.sum_mul, hXB r hr]
    rw [← eA, ← eB]
    exact Finset.sum_congr rfl fun i _ => hn i r hr
  set D := fun r => A.pressure r - B.pressure r
  have hDd : ∀ r, HasDerivAt D (-(A.massDensity r * A.g) - -(B.massDensity r * B.g)) r :=
    fun r => (hA.hasDerivAt_pressure r).sub (hB.hasDerivAt_pressure r)
  -- the pressure difference has zero derivative on the column
  have hD0 : ∀ r ∈ Set.Ico A.R0 Rtop, HasDerivWithinAt D 0 (Set.Ici r) r := fun r hr => by
    have := hDd r
    rw [show -(A.massDensity r * A.g) - -(B.massDensity r * B.g) = 0 by
      simp [massDensity, hN r (Set.Ico_subset_Icc_self hr), hm, hg]] at this
    exact this.hasDerivWithinAt
  have hcont : ContinuousOn D (Set.Icc A.R0 Rtop) :=
    fun r _ => (hDd r).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hD0
  intro r hr
  have hP : A.pressure r = B.pressure r := by
    have := hconst r hr
    simp only [D, pressure_R0, hR0] at this
    rw [← hR0, pressure_R0, hP0] at this
    linarith
  have h := hN r hr
  simp only [numberDensity, hP] at h
  have hpos := hB.pressure_pos r
  have hTA := hA.T_pos r
  have hTB := hB.T_pos r
  rw [div_eq_div_iff (mul_pos kB_pos hTA).ne' (mul_pos kB_pos hTB).ne'] at h
  have := mul_left_cancel₀ hpos.ne' h
  exact mul_left_cancel₀ kB_ne_zero this.symm

end Atmosphere

end ExoLean
