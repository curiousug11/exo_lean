# ExoLean: identifiability and degeneracy theorems for transmission spectra in Lean 4

This repository contains machine-checked theorems (Lean 4 + Mathlib) about **structural
identifiability** of exoplanet transmission spectra. The question is: given a noiseless,
continuous spectrum `R_p(λ)`, which atmospheric parameters `(T(P), VMR_i(P), R0, P0, g, κ_cloud)`
are uniquely recoverable, and which are linked by *exact* degeneracies?

Every result is proved from the definitions. There is **no `sorry`**, and the headline theorems
use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). You can check this
with `lake env lean scripts/CheckAxioms.lean`. Every degeneracy is **constructive**: the proof
builds the second atmosphere explicitly.

## Building

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
lake exe cache get      # prebuilt Mathlib
lake build              # builds ExoLean (Lean v4.35.0, Mathlib v4.35.0)
```

## Two forward operators, one assumption lattice

| Layer | File(s) | Forward operator `F : Θ → (λ ↦ R_p)` | Assumes isothermal / isochemical? |
|---|---|---|---|
| **Exact** | `Atmosphere.lean` | hydrostatic `P(r)`, ideal gas, exact chord integral `R_p² = R0² + 2∫ b(1−e^{−τ(b,λ)}) db`, `τ = 2∫ α r/√(r²−b²) dr` | **No**: arbitrary `T(r)`, `X_i(r)` |
| **Analytic** | `Analytic.lean` | Heng & Kitzmann (2017): `R_p = R0 + H[γ + ln(P0 κ(λ)/g · √(2πR0/H))]`, `κ = Σ (X_i/m) σ_i + κ_cloud` | Yes (and optically thick limit) |

The full assumption lattice is in `ExoLean/Assumptions.lean`. Structural assumptions are
catalogued in an `Assumption` type. Regime assumptions (`Isothermal`, `Isochemical`, `GreyOn`,
`PowerLaw`) are hypotheses that theorems take explicitly. The bridge lemma
`speciesDensity_of_isothermal_isochemical` proves that the isothermal + isochemical node of
the exact layer gives exponential densities with `H = k_B T/(m g)`, which is the input to the
analytic layer. `hasDerivAt_pressure` proves that the pressure profile really solves
`dP/dr = −ρ g`.

## Main results

### Exact layer: non-isothermal, non-isochemical

| Theorem | Statement |
|---|---|
| `Atmosphere.spectrum_eq_of_speciesDensity_eq` | The exact spectrum depends on the atmosphere **only** through `R0` and the active-species number densities `n_i(r)`. |
| **`Atmosphere.temperature_profile_unidentifiable`** | For **any** hydrostatic atmosphere and **any** continuous `T'(r) > 0`, there is a hydrostatic atmosphere with temperature exactly `T'`, the same `R0, P0, g, m`, mixing ratios `X'_i = X_i (T'/T)(P/P')`, and an identical spectrum for *every* cross-section set and truncation radius. |
| `Atmosphere.PhysicalVMR.retemper` | The compensating `X'_i` are admissible (`≥ 0`, `Σ ≤ 1`) when `T ≤ T' ≤ cT` and `c Σ X_i ≤ 1`. |
| **`Atmosphere.exists_inverted_twin`** | Explicit counterexample: a **normal** profile (`T` strictly decreasing outward) and a **thermally inverted** profile (strictly increasing). Both are non-isothermal and hydrostatic with admissible VMRs, and the spectra are identical. |
| `Atmosphere.isothermal_twin` | Isothermal + isochemical at `T0` ≡ isothermal at `cT0` with `X'(r) = cX exp(−(1−1/c)(r−R0)/H)`, which is *not* isochemical. So "temperature from the scale height" depends on the isochemical assumption. |
| `Atmosphere.T_eq_of_speciesDensity_eq` | Converse: if the composition is **closed** (`Σ X_i = 1`, no transparent filler), equal number densities on `[R0, Rtop]` force equal `T(r)` there. The degeneracy above therefore comes entirely from the spectrally invisible filler gas. |

### Analytic layer: Heng & Kitzmann (2017)

| Theorem | Statement |
|---|---|
| `Iso.transitRadius_eq` | `R_p(λ) = L(θ) + H ln κ(λ)`: parameters enter only through `H`, a level `L`, and `κ`. |
| `Iso.transitRadius_referenceGauge` | Exact `(R0, P0)` gauge: `P0' = P0 √(R0/R0') e^{(R0−R0')/H}`. The `√R0` factor is compensated exactly. |
| `Iso.transitRadius_normalization` | `(P0, X_i, κ_c) ↦ (P0/c, cX_i, cκ_c)` (Benneke & Seager 2012). |
| `Iso.transitRadius_T_g`, `Iso.transitRadius_T_m` | Only `T/g` and `T/m` are seen. |
| **`Iso.transitRadius_fibre`** | **Complete fibre description** (one absorber + grey cloud, band whose `σ`-image contains an interval): `F θ = F θ'` **iff** `H = H'`, `aκ'_c = a'κ_c`, `L = L' + H ln(a'/a)`. The identifiable coordinates are `(H, κ_c/a, L + H ln a)`, three out of seven parameters. |
| `Iso.temperature_identifiable`, `Iso.cloudRatio_identifiable`, `Iso.radius_identifiable_of_P0` | `T` is identifiable given `m, g`. `κ_c/a` is identifiable. `R0` is identifiable from one wavelength once `P0` is fixed. |
| `Iso.grey_temperature_unidentifiable` | Grey opacity: **every** `T' > 0` reproduces the flat spectrum exactly. |
| `Iso.lecavelier_slope` | `dR_p/d ln λ = β H` for power-law opacity (Lecavelier des Etangs et al. 2008). |
| `Iso.powerLaw_slope_degeneracy`, `Iso.slopeProduct_identifiable` | Free slope: `(T, β) ↦ (cT, β/c)` is exact, and only `βH` is identifiable. |
| `Iso.scaleHeight_eq_of_powerRigid` | Multi-absorber reduction: if the opacity cone is **power-rigid** (no positive power `κ^r`, `r ≠ 1`, of a non-constant cone element is proportional to a cone element), then `H` is identifiable. The physics question becomes a pure-mathematics one. |
| **`Iso.rayleigh_lambda8_twin`**, `Iso.not_powerRigid_rayleigh_lambda8` | Counterexample to "distinct cross-sections suffice": a pure `λ⁻⁴` Rayleigh scatterer at `T` and a pure `λ⁻⁸` absorber at `T/2` give identical spectra. |

## Open targets: status

| Target | Outcome | Key theorems |
|---|---|---|
| **3. `E₁` breaks the (R0, P0) gauge** | **Proved, for every admissible model.** The gauge shifts R_p by exactly `H·(E₁(τ₀e^{(R0−R0')/H}) − E₁(τ₀))`. This is nonzero whenever `R0' ≠ R0`, and positive when `R0' > R0`. Since `E₁(τ) ≤ e^{−τ}`, the breaking is exponentially weak in the optically thick regime. | `expIntegralE1_strictAntiOn`, `Iso.transitRadiusE1_referenceGauge`, `Iso.transitRadiusE1_gauge_ne`, `Iso.transitRadiusE1_gauge_lt`, `referenceGaugeBrokenByE1` (`E1Gauge.lean`) |
| **2. Gaussian bands are power-rigid** | **Original statement disproved.** It allowed exponent `r = 0`, and a constant cloud satisfies `κ' = C κ⁰` for any `κ`, so the original definition could never hold. `PowerRigid` now requires `r, C > 0`, which is all the physics uses; the reduction theorem and the λ⁻⁴/λ⁻⁸ counterexample are unchanged. **Corrected statement proved for a single band** (any continuous positive cross-section + grey cloud). The multi-band case is still open; a proof sketch is in the file. | `not_gaussianBandsPowerRigidUnrestricted`, `powerRigid_of_unique`, `gaussianBandsPowerRigid_of_unique` (`GaussianRigidity.lean`) |
| **1. Spectrum ⇒ density profiles** | **Original statement disproved** for every cross-section set: it allowed a zero-thickness column (`R0 = Rtop`). **Corrected statement** (`R0 < Rtop`, continuous X) is **disproved whenever two species have proportional cross-sections** on the band (moving column between them leaves the extinction unchanged). Still open for non-proportional cross-sections. For one species, the spectrum is a Laplace-type transform of the column-density distribution, so uniqueness is expected only up to rearrangement (e.g. for monotone profiles). | `not_densityProfilesIdentifiable`, `not_densityProfilesIdentifiableCts_of_proportional` (`DensityTargets.lean`); `temperature_identifiable_of_densityIdentifiable` now uses the corrected target |

## Numerical cross-check (not part of the proofs)

`python3 scripts/numerical_check.py` (requires numpy and scipy) mirrors the Lean definitions
for a hot Jupiter (`H ≈ 434 km`):

- Where `τ₀ > 10`, HK17 agrees with the exact chord integral to `0.03 H`. Where `τ₀ < 1`, HK17
  is off by several `H` (this is the `E₁` regime of open target 3).
- The inverted twin's transit depth matches the normal atmosphere's to floating-point
  precision. Without the VMR compensation, the same inversion changes the depth by ~190 ppm.
- The isothermal twin's depths agree to ~10⁻¹¹ ppm.

## Scope and caveats

- The HK17 formula is the *definition* of the analytic operator. Its asymptotic derivation
  from the exact integral is not formalised.
- The exact layer assumes T,P-independent cross-sections, a transparent filler gas, constant
  `g` and `m`, no refraction, an opaque surface at `R0`, and truncation at `Rtop`. The profile
  degeneracy needs the first two. Collision-induced absorption or Rayleigh scattering by the
  background breaks it (see `T_eq_of_speciesDensity_eq`).
- `transitRadiusE1` keeps HK17's `E₁(τ₀)` term but is still taken as a definition.

## References

- Lecavelier des Etangs, A., Pont, F., Vidal-Madjar, A., et al. (2008). Rayleigh scattering in the transit spectrum of HD 189733b. *A&A*, 481, L83. https://doi.org/10.1051/0004-6361:200809388
- Heng, K., & Kitzmann, D. (2017). The theory of transmission spectra revisited. *MNRAS*, 470, 2972. https://doi.org/10.1093/mnras/stx1453
- Benneke, B., & Seager, S. (2012). Atmospheric retrieval for super-Earths. *ApJ*, 753, 100. https://doi.org/10.1088/0004-637X/753/2/100
- de Wit, J., & Seager, S. (2013). Constraining exoplanet mass from transmission spectroscopy. *Science*, 342, 1473. https://doi.org/10.1126/science.1245450
- Griffith, C. A. (2014). Disentangling degenerate solutions from primary transit and secondary eclipse spectroscopy of exoplanets. *Phil. Trans. R. Soc. A*, 372, 20130086. https://doi.org/10.1098/rsta.2013.0086
- Welbanks, L., & Madhusudhan, N. (2019). On degeneracies in retrievals of exoplanetary transmission spectra. *AJ*, 157, 206. https://doi.org/10.3847/1538-3881/ab14de
