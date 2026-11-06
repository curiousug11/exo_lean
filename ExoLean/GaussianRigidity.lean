import ExoLean.OpenProblems

/-!
# Target 2: power rigidity of Gaussian bands

**The original target was false, for a trivial reason** (`not_gaussianBandsPowerRigidUnrestricted`).
As first stated, power rigidity allowed the exponent `r = 0`. Then the constant cloud
opacity `κ' ≡ 1` satisfies `κ' = 1 · κ⁰` for *every* `κ`, so no family with a non-constant
cone element could ever be power-rigid (`not_powerRigidUnrestricted`). The reduction theorem
`Iso.scaleHeight_eq_of_powerRigid` only ever uses `r = H/H' > 0` and `C > 0`. So the
definition `PowerRigid` has been corrected to require them, and the reduction theorem and the
`λ⁻⁴ / λ⁻⁸` counterexample hold unchanged.

**Corrected target: proved for a single band.**
`powerRigid_of_unique` shows that *any* single continuous positive cross-section, plus a grey
cloud, is power-rigid on every open band. In particular `GaussianBandsPowerRigid` holds when
there is at most one band (`gaussianBandsPowerRigid_of_unique`,
`gaussianBandsPowerRigid_of_isEmpty`). The proof uses the intermediate value theorem to turn
the band into an interval of cross-section values, then applies the log-affine rigidity lemma.

The multi-band case (`|ι| ≥ 2`) remains open in Lean. A proof strategy (not formalised):
(i) both sides are real-analytic on `ℝ` and `f > 0` everywhere, so the identity `g = C f^r`
extends from the band to all of `ℝ`; (ii) as `λ → ∞` there is a unique slowest-decaying
active band `i*` (largest width, then largest centre). Matching asymptotics then forces a band
centred at `c_{i*}` with width `s_{i*}/√r` (cloud-free case), or with width `s_{i*}/√2` (from
the `u²` term of `(1+u)^r`, cloudy case). Injectivity of the centres makes that band `i*`
itself, which contradicts `r ≠ 1`.
-/

noncomputable section

open Real Set

namespace ExoLean

open OpenProblems

variable {ι : Type*} [Fintype ι]

/-- The original (too strong) formulation of power rigidity, which also allowed `r ≤ 0` and
`C ≤ 0`. -/
def PowerRigidUnrestricted (σ : ι → ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ κ ∈ opacityCone σ, ∀ κ' ∈ opacityCone σ, ∀ r C : ℝ,
    (∀ w ∈ S, 0 < κ w) → (∀ w ∈ S, κ' w = C * κ w ^ r) →
    (∃ w₁ ∈ S, ∃ w₂ ∈ S, κ w₁ ≠ κ w₂) → r = 1

/-- The unrestricted formulation fails as soon as the cone has a positive non-constant
element: take `κ' ≡ 1`, `r = 0`, `C = 1`. -/
theorem not_powerRigidUnrestricted {σ : ι → ℝ → ℝ} {S : Set ℝ} {κ : ℝ → ℝ}
    (hκ : κ ∈ opacityCone σ) (hpos : ∀ w ∈ S, 0 < κ w)
    (hnc : ∃ w₁ ∈ S, ∃ w₂ ∈ S, κ w₁ ≠ κ w₂) : ¬ PowerRigidUnrestricted σ S := by
  intro h
  have := h κ hκ (fun _ => 1) ⟨fun _ => 0, 1, fun _ => le_rfl, zero_le_one, fun w => by simp⟩
    0 1 hpos (fun w _ => by simp) hnc
  norm_num at this

/-- The original Target 2. -/
def GaussianBandsPowerRigidUnrestricted : Prop :=
  ∀ (c s : ι → ℝ), Function.Injective c → (∀ i, 0 < s i) →
    ∀ l u : ℝ, l < u → PowerRigidUnrestricted (gaussianBands c s) (Ioo l u)

/-- **The original Target 2 is false** (for any nonempty set of bands). -/
theorem not_gaussianBandsPowerRigidUnrestricted [Nonempty ι] :
    ¬ GaussianBandsPowerRigidUnrestricted (ι := ι) := by
  classical
  intro h
  obtain ⟨i0⟩ := ‹Nonempty ι›
  let c : ι → ℝ := fun i => (Fintype.equivFin ι i : ℕ)
  have hc : Function.Injective c := fun i j hij => by
    simp only [c, Nat.cast_inj] at hij
    exact (Fintype.equivFin ι).injective (Fin.ext hij)
  have h' := h c (fun _ => 1) hc (fun _ => one_pos) (c i0) (c i0 + 1) (by linarith)
  refine not_powerRigidUnrestricted (σ := gaussianBands c fun _ => 1)
    (S := Ioo (c i0) (c i0 + 1)) (κ := gaussianBands c (fun _ => 1) i0)
    ⟨fun i => if i = i0 then 1 else 0, 0, fun i => by dsimp only; split_ifs <;> norm_num, le_rfl,
      fun w => by simp⟩
    (fun w _ => exp_pos _)
    ⟨c i0 + 1/4, ⟨by linarith, by linarith⟩, c i0 + 1/2, ⟨by linarith, by linarith⟩, ?_⟩ h'
  simp only [gaussianBands, div_one, add_sub_cancel_left]
  intro heq
  have := exp_injective heq
  norm_num at this

/-- **Single-band power rigidity.** One continuous, positive cross-section plus a grey cloud is
power-rigid on every open band. -/
theorem powerRigid_of_unique [Unique ι] {σ : ι → ℝ → ℝ} {l u : ℝ}
    (hcont : ContinuousOn (σ default) (Ioo l u)) (hpos : ∀ w ∈ Ioo l u, 0 < σ default w) :
    PowerRigid σ (Ioo l u) := by
  rintro κ ⟨a, c0, ha, hc0, hκ⟩ κ' ⟨b, c1, hb, hc1, hκ'⟩ r C hr hC hκpos heq
    ⟨w1, hw1, w2, hw2, hne⟩
  simp only [Fintype.sum_unique] at hκ hκ'
  set A := a default
  set B := b default
  set φ := σ default
  have hφne : φ w1 ≠ φ w2 := fun h => hne (by rw [hκ, hκ, h])
  have hA : 0 < A := by
    rcases (ha default).lt_or_eq with h | h
    · exact h
    · have hA0 : A = 0 := h.symm
      exact absurd (by rw [hκ, hκ, hA0]; ring) hne
  have hB : 0 < B := by
    rcases (hb default).lt_or_eq with h | h
    · exact h
    · exfalso
      have e1 := heq w1 hw1
      have e2 := heq w2 hw2
      have hB0 : B = 0 := h.symm
      rw [hκ', hB0, zero_mul, zero_add] at e1 e2
      have : κ w1 ^ r = κ w2 ^ r := mul_left_cancel₀ hC.ne' (e1.symm.trans e2)
      have := congrArg (· ^ r⁻¹) this
      simp only [rpow_rpow_inv (hκpos w1 hw1).le hr.ne',
        rpow_rpow_inv (hκpos w2 hw2).le hr.ne'] at this
      exact hne this
  -- the cross-section takes every value between `φ w1` and `φ w2`
  have hsub : Ioo (min (φ w1) (φ w2)) (max (φ w1) (φ w2)) ⊆ φ '' Ioo l u := by
    intro y hy
    have hu : uIcc w1 w2 ⊆ Ioo l u := ordConnected_Ioo.uIcc_subset hw1 hw2
    obtain ⟨w, hw, rfl⟩ := intermediate_value_uIcc (hcont.mono hu) (Ioo_subset_Icc_self hy)
    exact ⟨w, hu hw, rfl⟩
  have hmin : 0 ≤ min (φ w1) (φ w2) := le_min (hpos w1 hw1).le (hpos w2 hw2).le
  have hlt : min (φ w1) (φ w2) < max (φ w1) (φ w2) := min_lt_max.mpr hφne
  have key := logAffine_rigidity (L := log C) (L' := 0) (H' := 1) hA hB hc0 hc1 hr hmin hlt
    (fun y hy => by
      obtain ⟨w, hw, rfl⟩ := hsub hy
      have e := heq w hw
      rw [hκ, hκ'] at e
      have hbase : 0 < A * φ w + c0 := by have := hpos w hw; positivity
      rw [e, log_mul hC.ne' (rpow_pos_of_pos hbase r).ne', log_rpow hbase]
      ring)
  exact key.1

omit [Fintype ι] in
theorem continuous_gaussianBands (c s : ι → ℝ) (i : ι) : Continuous (gaussianBands c s i) := by
  unfold gaussianBands; fun_prop

/-- **Corrected Target 2, single band.** -/
theorem gaussianBandsPowerRigid_of_unique [Unique ι] : GaussianBandsPowerRigid (ι := ι) :=
  fun c s _ _ _ _ _ => powerRigid_of_unique (continuous_gaussianBands c s default).continuousOn
    (fun _ _ => exp_pos _)

/-- **Corrected Target 2, no bands** (the cone is then just the grey cloud). -/
theorem gaussianBandsPowerRigid_of_isEmpty [IsEmpty ι] : GaussianBandsPowerRigid (ι := ι) := by
  rintro c s - - l u - κ ⟨a, c0, -, -, hκ⟩ κ' - r C - - - - ⟨w1, -, w2, -, hne⟩
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hκ
  exact absurd (by rw [hκ, hκ]) hne

end ExoLean
