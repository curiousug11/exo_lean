import ExoLean.Analytic

/-!
# Structural identifiability of the analytic operator

**Main theorem** (`Iso.transitRadius_fibre`). Take one absorber with a known cross-section
shape `σ` plus a grey cloud, observed on a wavelength set `S` such that `σ(S)` contains an
open interval. Then two admissible parameter sets give the same noiseless spectrum on `S`
**if and only if**
```
H = H',     a κ'_c = a' κ_c,     L = L' + H ln(a'/a)          (a = X/m).
```
This describes every fibre of the forward map `F : Θ → (S → ℝ)`, so it is a complete
identifiability statement. The identifiable coordinates are
`(H, κ_c / a, L + H ln a)`, three numbers, out of the seven parameters
`(T, m, g, R0, P0, X, κ_c)`. The other four directions are exactly the gauge orbits of
`ExoLean.Analytic`.

Corollaries:

* `Iso.scaleHeight_identifiable`: `H = k_B T/(m g)` is identifiable;
* `Iso.temperature_identifiable`: with `m` and `g` known, `T` is identifiable;
* `Iso.cloudRatio_identifiable`: the cloud-to-absorber opacity ratio is identifiable;
* `Iso.radius_identifiable_of_P0`: with every other parameter fixed (in particular `P0`),
  `R0` is identifiable from a single wavelength.

The analytic heart is `logAffine_rigidity`, a rigidity lemma for functions of the form
`u ↦ L + H log(a u + κ)`. It is proved by comparing derivatives on an open interval.
-/

noncomputable section

open Real Filter Topology

set_option linter.unusedSectionVars false

namespace ExoLean

/-- Derivative of the log-affine profile `u ↦ L + H log(a u + κ)`. -/
theorem hasDerivAt_logAffine {L H a κ u : ℝ} (hpos : 0 < a * u + κ) :
    HasDerivAt (fun u => L + H * log (a * u + κ)) (H * (a / (a * u + κ))) u := by
  have h := (((hasDerivAt_id' u).const_mul a).add_const κ).log hpos.ne'
  simpa using (h.const_mul H).const_add L

/-- **Rigidity of log-affine profiles.** If `L + H log(a u + κ) = L' + H' log(a' u + κ')` on a
nonempty open interval of positive `u`, then `H = H'`, `a κ' = a' κ` and
`L = L' + H log(a'/a)`. -/
theorem logAffine_rigidity {L L' H H' a a' κ κ' u1 u2 : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') (hH : 0 < H) (hu1 : 0 ≤ u1) (h12 : u1 < u2)
    (h : ∀ u ∈ Set.Ioo u1 u2, L + H * log (a * u + κ) = L' + H' * log (a' * u + κ')) :
    H = H' ∧ a * κ' = a' * κ ∧ L = L' + H * log (a' / a) := by
  -- equality of derivatives on the interval
  have hderiv : ∀ u ∈ Set.Ioo u1 u2, H * a * (a' * u + κ') = H' * a' * (a * u + κ) := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt hu1 hu.1
    have hp : 0 < a * u + κ := by positivity
    have hp' : 0 < a' * u + κ' := by positivity
    have heq : (fun u => L + H * log (a * u + κ)) =ᶠ[𝓝 u]
        (fun u => L' + H' * log (a' * u + κ')) :=
      eventually_of_mem (Ioo_mem_nhds hu.1 hu.2) h
    have hd := (hasDerivAt_logAffine (L := L) (H := H) hp).unique
      ((hasDerivAt_logAffine (L := L') (H := H') hp').congr_of_eventuallyEq heq)
    field_simp at hd
    linarith [hd]
  set v1 := u1 + (u2 - u1) / 3
  set v2 := u1 + 2 * (u2 - u1) / 3
  have hv1 : v1 ∈ Set.Ioo u1 u2 := ⟨by simp only [v1]; linarith, by simp only [v1]; linarith⟩
  have hv2 : v2 ∈ Set.Ioo u1 u2 := ⟨by simp only [v2]; linarith, by simp only [v2]; linarith⟩
  have e1 := hderiv v1 hv1
  have e2 := hderiv v2 hv2
  have hHH : H = H' := by
    have h0 : (H - H') * (a * a') * (v1 - v2) = 0 := by linear_combination e1 - e2
    have hv : v1 - v2 ≠ 0 := by simp only [v1, v2]; intro h; linarith
    have := (mul_eq_zero.mp h0).resolve_right hv
    have := (mul_eq_zero.mp this).resolve_right (mul_pos ha ha').ne'
    linarith
  subst hHH
  have hκκ : a * κ' = a' * κ := by
    have h0 : H * (a * κ' - a' * κ) = 0 := by linear_combination e1
    have := (mul_eq_zero.mp h0).resolve_left hH.ne'
    linarith
  refine ⟨rfl, hκκ, ?_⟩
  have hv0 : 0 < v1 := lt_of_le_of_lt hu1 hv1.1
  have hy : 0 < a * v1 + κ := by positivity
  have hfac : a' * v1 + κ' = a' / a * (a * v1 + κ) := by
    field_simp
    linear_combination hκκ
  have := h v1 hv1
  rw [hfac, log_mul (div_pos ha' ha).ne' hy.ne'] at this
  linarith

/-- Converse of `logAffine_rigidity`: the three relations imply equality of the profiles. -/
theorem logAffine_eq_of {L L' H a a' κ κ' u : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hpos : 0 < a * u + κ) (hκκ : a * κ' = a' * κ) (hL : L = L' + H * log (a' / a)) :
    L + H * log (a * u + κ) = L' + H * log (a' * u + κ') := by
  have hfac : a' * u + κ' = a' / a * (a * u + κ) := by
    field_simp
    linear_combination hκκ
  rw [hfac, log_mul (div_pos ha' ha).ne' hpos.ne', hL]
  ring

namespace Iso

variable {ι : Type*} [Fintype ι] [Unique ι] {p q : Iso ι}

theorem opacity_unique (p : Iso ι) (σ : ι → ℝ → ℝ) (w : ℝ) :
    p.opacity σ w = p.absCoeff default * σ default w + p.κc := by
  simp [opacity]

/-- **Complete description of the fibres of the analytic forward map**
(single absorber + grey cloud). -/
theorem transitRadius_fibre (hp : p.Valid) (hq : q.Valid)
    (hXp : 0 < p.X default) (hXq : 0 < q.X default)
    {σ : ι → ℝ → ℝ} {S : Set ℝ} (hσ : ∀ w ∈ S, 0 < σ default w)
    {u1 u2 : ℝ} (hu1 : 0 ≤ u1) (h12 : u1 < u2) (hsub : Set.Ioo u1 u2 ⊆ σ default '' S) :
    (∀ w ∈ S, p.transitRadius σ w = q.transitRadius σ w) ↔
      p.H = q.H ∧ p.absCoeff default * q.κc = q.absCoeff default * p.κc ∧
        p.level = q.level + p.H * log (q.absCoeff default / p.absCoeff default) := by
  have ha : 0 < p.absCoeff default := div_pos hXp hp.m_pos
  have ha' : 0 < q.absCoeff default := div_pos hXq hq.m_pos
  have hκpos : ∀ (r : Iso ι), r.Valid → 0 < r.absCoeff default → ∀ w ∈ S,
      0 < r.opacity σ w := fun r hr har w hw => by
    rw [opacity_unique]
    have := hσ w hw
    have := hr.κc_nonneg
    positivity
  constructor
  · intro h
    apply logAffine_rigidity ha ha' hp.κc_nonneg hq.κc_nonneg hp.H_pos hu1 h12
    intro u hu
    obtain ⟨w, hw, rfl⟩ := hsub hu
    have := h w hw
    rwa [transitRadius_eq hp (hκpos p hp ha w hw), transitRadius_eq hq (hκpos q hq ha' w hw),
      opacity_unique, opacity_unique] at this
  · rintro ⟨hH, hκκ, hL⟩ w hw
    rw [transitRadius_eq hp (hκpos p hp ha w hw), transitRadius_eq hq (hκpos q hq ha' w hw),
      opacity_unique, opacity_unique, ← hH]
    exact logAffine_eq_of ha ha' (by rw [← opacity_unique]; exact hκpos p hp ha w hw) hκκ hL

/-- The scale height `H = k_B T/(m g)` is identifiable. -/
theorem scaleHeight_identifiable (hp : p.Valid) (hq : q.Valid)
    (hXp : 0 < p.X default) (hXq : 0 < q.X default)
    {σ : ι → ℝ → ℝ} {S : Set ℝ} (hσ : ∀ w ∈ S, 0 < σ default w)
    {u1 u2 : ℝ} (hu1 : 0 ≤ u1) (h12 : u1 < u2) (hsub : Set.Ioo u1 u2 ⊆ σ default '' S)
    (h : ∀ w ∈ S, p.transitRadius σ w = q.transitRadius σ w) : p.H = q.H :=
  ((transitRadius_fibre hp hq hXp hXq hσ hu1 h12 hsub).mp h).1

/-- With the mean molecular mass and the gravity known, the temperature is identifiable. -/
theorem temperature_identifiable (hp : p.Valid) (hq : q.Valid)
    (hXp : 0 < p.X default) (hXq : 0 < q.X default)
    {σ : ι → ℝ → ℝ} {S : Set ℝ} (hσ : ∀ w ∈ S, 0 < σ default w)
    {u1 u2 : ℝ} (hu1 : 0 ≤ u1) (h12 : u1 < u2) (hsub : Set.Ioo u1 u2 ⊆ σ default '' S)
    (hm : p.m = q.m) (hg : p.g = q.g)
    (h : ∀ w ∈ S, p.transitRadius σ w = q.transitRadius σ w) : p.T = q.T := by
  have hH := scaleHeight_identifiable hp hq hXp hXq hσ hu1 h12 hsub h
  have hmg : 0 < q.m * q.g := mul_pos hq.m_pos hq.g_pos
  have h' : kB * p.T / (p.m * p.g) = kB * q.T / (q.m * q.g) := hH
  rw [hm, hg, div_left_inj' hmg.ne'] at h'
  exact mul_left_cancel₀ kB_ne_zero h'

/-- The cloud-to-absorber opacity ratio `κ_c / a` is identifiable. -/
theorem cloudRatio_identifiable (hp : p.Valid) (hq : q.Valid)
    (hXp : 0 < p.X default) (hXq : 0 < q.X default)
    {σ : ι → ℝ → ℝ} {S : Set ℝ} (hσ : ∀ w ∈ S, 0 < σ default w)
    {u1 u2 : ℝ} (hu1 : 0 ≤ u1) (h12 : u1 < u2) (hsub : Set.Ioo u1 u2 ⊆ σ default '' S)
    (h : ∀ w ∈ S, p.transitRadius σ w = q.transitRadius σ w) :
    p.κc / p.absCoeff default = q.κc / q.absCoeff default := by
  have ha : 0 < p.absCoeff default := div_pos hXp hp.m_pos
  have ha' : 0 < q.absCoeff default := div_pos hXq hq.m_pos
  have := ((transitRadius_fibre hp hq hXp hXq hσ hu1 h12 hsub).mp h).2.1
  rw [div_eq_div_iff ha.ne' ha'.ne']
  linarith

end Iso

/-! ### Identifiability of `R0` once the reference pressure is fixed -/

namespace Iso

variable {ι : Type*} [Fintype ι]

/-- With all other parameters fixed (in particular the reference pressure `P0`), the
transit radius at a single wavelength is strictly increasing in `R0`. -/
theorem transitRadius_strictMonoOn_R0 (p : Iso ι) (hp : p.Valid) (σ : ι → ℝ → ℝ) (w : ℝ)
    (hκ : 0 < p.opacity σ w) :
    StrictMonoOn (fun R => ({ p with R0 := R } : Iso ι).transitRadius σ w) (Set.Ioi 0) := by
  intro R hR R' hR' hlt
  have hH := hp.H_pos
  have hR0 : (0 : ℝ) < R := hR
  simp only [transitRadius, H, opacity, absCoeff]
  have harg : 0 < p.P0 * p.opacity σ w / p.g := div_pos (mul_pos hp.P0_pos hκ) hp.g_pos
  have hs : 0 < √(2 * π * R / p.H) := Real.sqrt_pos.mpr (by positivity)
  have hle : log (p.P0 * p.opacity σ w / p.g * √(2 * π * R / p.H)) ≤
      log (p.P0 * p.opacity σ w / p.g * √(2 * π * R' / p.H)) := by
    apply log_le_log (mul_pos harg hs)
    apply mul_le_mul_of_nonneg_left _ harg.le
    apply sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hH.le
    nlinarith [pi_pos]
  have := mul_le_mul_of_nonneg_left (add_le_add_left hle γE) hH.le
  simp only [H, opacity, absCoeff] at this harg ⊢
  linarith

/-- **`R0` is identifiable once `P0` is fixed**, even from a single wavelength. -/
theorem radius_identifiable_of_P0 (p : Iso ι) (hp : p.Valid) {R R' : ℝ} (hR : 0 < R)
    (hR' : 0 < R') (σ : ι → ℝ → ℝ) (w : ℝ) (hκ : 0 < p.opacity σ w)
    (h : ({ p with R0 := R } : Iso ι).transitRadius σ w =
      ({ p with R0 := R' } : Iso ι).transitRadius σ w) : R = R' :=
  (transitRadius_strictMonoOn_R0 p hp σ w hκ).injOn hR hR' h

end Iso

end ExoLean
