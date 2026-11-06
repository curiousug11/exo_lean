import ExoLean.Assumptions

/-!
# Exact temperature–abundance-profile degeneracy (non-isothermal, non-isochemical)

**Main theorem** (`Atmosphere.temperature_profile_unidentifiable`).
Work in the exact forward model, *without* the isothermal or isochemical assumptions.
Take any hydrostatic atmosphere `A` and **any** other continuous positive temperature
profile `T'(r)`. Then there is a second hydrostatic atmosphere `A'` with the same
`R0, P0, g, m` and temperature profile exactly `T'`, whose mixing-ratio profiles are
```
X'ᵢ(r) = Xᵢ(r) · (T'(r)/T(r)) · (P(r)/P'(r)),
```
and whose transmission spectrum is identical to that of `A`, at every wavelength, for every
choice of (T,P-independent) cross-sections and every truncation radius.

So, in this regime, a transmission spectrum carries **no** information about the temperature
profile on its own: any `T(r)` can be traded exactly for compensating `Xᵢ(r)` profiles. The
only thing the spectrum constrains is the active-species number-density profiles `nᵢ(r)`.
The proof is constructive, so it gives the second atmosphere explicitly.

Explicit instances:

* `Atmosphere.isothermal_twin`: an isothermal, isochemical atmosphere at `T0` is identical in
  transmission to an isothermal atmosphere at `c·T0` whose absorbers are depleted upward as
  `X'(r) = c X exp(-(1 - 1/c)(r - R0)/H)`. It is not isochemical when `c ≠ 1`. This is the
  precise sense in which "temperature from the scale height" relies on the isochemical
  assumption.
* `Atmosphere.exists_inverted_twin`: a non-inverted and a **thermally inverted** atmosphere,
  both non-isothermal and both with physically admissible mixing ratios
  (`0 ≤ Xᵢ`, `Σ Xᵢ ≤ 1`), giving the same exact spectrum.

How the degeneracy is broken: it needs (i) T,P-independent cross-sections and (ii) a
transparent filler gas whose density is not observed. With a spectrally active background
(H₂ Rayleigh scattering or collision-induced absorption), the filler density
`n(1 - Σ Xᵢ)` would also have to be preserved. That forces `Σ Xᵢ` to stay fixed, and the
construction breaks.
-/

noncomputable section

open Real

namespace ExoLean

namespace Atmosphere

variable {ι : Type*} (A : Atmosphere ι)

/-- Same atmosphere with temperature profile replaced by `T'` (mixing ratios unchanged). -/
def withT (T' : ℝ → ℝ) : Atmosphere ι := { A with T := T' }

/-- The compensating factor `(T'/T)·(P/P')` applied to all mixing ratios. -/
def compensation (T' : ℝ → ℝ) (r : ℝ) : ℝ :=
  (T' r / A.T r) * (A.pressure r / (A.withT T').pressure r)

/-- The **re-tempered twin** of `A`: temperature `T'`, mixing ratios rescaled by
`compensation`. -/
def retemper (T' : ℝ → ℝ) : Atmosphere ι :=
  { A with T := T', X := fun i r => A.X i r * A.compensation T' r }

variable {A} {T' : ℝ → ℝ}

@[simp] theorem retemper_T : (A.retemper T').T = T' := rfl
@[simp] theorem retemper_R0 : (A.retemper T').R0 = A.R0 := rfl
@[simp] theorem retemper_P0 : (A.retemper T').P0 = A.P0 := rfl
@[simp] theorem retemper_g : (A.retemper T').g = A.g := rfl
@[simp] theorem retemper_m : (A.retemper T').m = A.m := rfl
theorem retemper_X (i : ι) (r : ℝ) :
    (A.retemper T').X i r = A.X i r * A.compensation T' r := rfl
theorem retemper_pressure : (A.retemper T').pressure = (A.withT T').pressure := rfl

theorem pressure_pos_of_P0_pos (h : 0 < A.P0) (r : ℝ) : 0 < A.pressure r :=
  mul_pos h (exp_pos _)

/-- The re-tempered twin has exactly the same species number densities. -/
theorem speciesDensity_retemper (hA : A.WellPosed) (hT' : ∀ r, 0 < T' r) (i : ι) (r : ℝ) :
    (A.retemper T').speciesDensity i r = A.speciesDensity i r := by
  have hP' : 0 < (A.withT T').pressure r := pressure_pos_of_P0_pos (A := A.withT T') hA.P0_pos r
  have hT := hA.T_pos r
  have hTr := hT' r
  simp only [speciesDensity, numberDensity, retemper_pressure, retemper_X, compensation,
    retemper_T]
  field_simp

/-- The re-tempered twin is again a well-posed hydrostatic atmosphere. -/
theorem WellPosed.retemper (hA : A.WellPosed) (hc : Continuous T') (hT' : ∀ r, 0 < T' r) :
    (A.retemper T').WellPosed :=
  ⟨hA.P0_pos, hA.g_pos, hA.m_pos, hT', hc⟩

section Spectrum

variable [Fintype ι]

/-- The re-tempered twin has exactly the same transmission spectrum. -/
theorem spectrum_retemper (hA : A.WellPosed) (hT' : ∀ r, 0 < T' r)
    (σ : ι → ℝ → ℝ) (Rtop : ℝ) :
    (A.retemper T').spectrum σ Rtop = A.spectrum σ Rtop :=
  spectrum_eq_of_speciesDensity_eq (A := A.retemper T') (B := A) rfl
    (speciesDensity_retemper hA hT') σ Rtop

/-- **Main theorem: the temperature profile is not identifiable.**
For every hydrostatic atmosphere `A` and every continuous positive temperature profile `T'`,
there is a hydrostatic atmosphere with temperature profile exactly `T'`, the same
`R0, P0, g, m`, and the same transmission spectrum for all cross-sections and truncation
radii. -/
theorem temperature_profile_unidentifiable (hA : A.WellPosed) (T' : ℝ → ℝ)
    (hc : Continuous T') (hT' : ∀ r, 0 < T' r) :
    ∃ A' : Atmosphere ι, A'.WellPosed ∧ A'.T = T' ∧
      A'.R0 = A.R0 ∧ A'.P0 = A.P0 ∧ A'.g = A.g ∧ A'.m = A.m ∧
      (∀ i r, A'.speciesDensity i r = A.speciesDensity i r) ∧
      ∀ σ Rtop, A'.spectrum σ Rtop = A.spectrum σ Rtop :=
  ⟨A.retemper T', hA.retemper hc hT', rfl, rfl, rfl, rfl, rfl,
    speciesDensity_retemper hA hT', spectrum_retemper hA hT'⟩

end Spectrum

/-! ### Physical admissibility of the compensating mixing ratios -/

/-- A hotter atmosphere is more extended: if `T ≤ T'` on `[R0, r]` then `P(r) ≤ P'(r)`. -/
theorem pressure_le_withT (hA : A.WellPosed) (hc : Continuous T') (hT' : ∀ r, 0 < T' r)
    {r : ℝ} (hr : A.R0 ≤ r) (hle : ∀ s ∈ Set.Icc A.R0 r, A.T s ≤ T' s) :
    A.pressure r ≤ (A.withT T').pressure r := by
  have hA' : (A.withT T').WellPosed := ⟨hA.P0_pos, hA.g_pos, hA.m_pos, hT', hc⟩
  have hint : ∫ s in A.R0..r, (A.withT T').invScaleHeight s ≤
      ∫ s in A.R0..r, A.invScaleHeight s := by
    apply intervalIntegral.integral_mono_on hr
      (hA'.continuous_invScaleHeight.intervalIntegrable _ _)
      (hA.continuous_invScaleHeight.intervalIntegrable _ _)
    intro s hs
    simp only [invScaleHeight, withT]
    exact div_le_div_of_nonneg_left (mul_pos hA.m_pos hA.g_pos).le
      (mul_pos kB_pos (hA.T_pos s)) (mul_le_mul_of_nonneg_left (hle s hs) kB_pos.le)
  simp only [pressure]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by simpa [withT] using hint)) hA.P0_pos.le

theorem compensation_nonneg (hA : A.WellPosed) (hT' : ∀ r, 0 < T' r) (r : ℝ) :
    0 ≤ A.compensation T' r :=
  mul_nonneg (div_pos (hT' r) (hA.T_pos r)).le
    (div_pos (hA.pressure_pos r) (pressure_pos_of_P0_pos (A := A.withT T') hA.P0_pos r)).le

/-- If `T ≤ T' ≤ c T` on `[R0, r]` then the compensating factor is at most `c`. -/
theorem compensation_le (hA : A.WellPosed) (hc : Continuous T') (hT' : ∀ r, 0 < T' r)
    {c r : ℝ} (hr : A.R0 ≤ r) (hle : ∀ s ∈ Set.Icc A.R0 r, A.T s ≤ T' s)
    (hup : T' r ≤ c * A.T r) : A.compensation T' r ≤ c := by
  have hP' := pressure_pos_of_P0_pos (A := A.withT T') hA.P0_pos r
  have h1 : T' r / A.T r ≤ c := (div_le_iff₀ (hA.T_pos r)).mpr hup
  have h2 : A.pressure r / (A.withT T').pressure r ≤ 1 :=
    (div_le_one hP').mpr (pressure_le_withT hA hc hT' hr hle)
  have := mul_le_mul h1 h2 (div_pos (hA.pressure_pos r) hP').le
    ((div_pos (hT' r) (hA.T_pos r)).le.trans h1)
  simpa [compensation] using this

variable [Fintype ι] in
/-- **Physical admissibility.** If `A` has admissible mixing ratios, `T ≤ T' ≤ c T` above `R0`,
and `c · Σᵢ Xᵢ ≤ 1` above `R0` (true for trace absorbers), then the twin's mixing ratios are
admissible too. -/
theorem PhysicalVMR.retemper (hA : A.WellPosed) (hvmr : A.PhysicalVMR) (hc : Continuous T')
    (hT' : ∀ r, 0 < T' r) {c : ℝ}
    (hle : ∀ s, A.R0 ≤ s → A.T s ≤ T' s) (hup : ∀ s, A.R0 ≤ s → T' s ≤ c * A.T s)
    (hsum : ∀ s, A.R0 ≤ s → c * ∑ i, A.X i s ≤ 1) :
    (A.retemper T').PhysicalVMR := by
  intro r hr
  obtain ⟨hX0, hX1⟩ := hvmr r hr
  have hcomp0 := compensation_nonneg hA hT' r
  have hcomp := compensation_le hA hc hT' hr (fun s hs => hle s hs.1) (hup r hr)
  refine ⟨fun i => mul_nonneg (hX0 i) hcomp0, ?_⟩
  simp only [retemper_X, ← Finset.sum_mul]
  calc (∑ i, A.X i r) * A.compensation T' r ≤ (∑ i, A.X i r) * c :=
        mul_le_mul_of_nonneg_left hcomp (Finset.sum_nonneg fun i _ => hX0 i)
    _ = c * ∑ i, A.X i r := mul_comm _ _
    _ ≤ 1 := hsum r hr

end Atmosphere

end ExoLean
