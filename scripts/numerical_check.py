"""Numerical cross-check of the Lean definitions (not part of the proofs).

Mirrors `ExoLean.Atmosphere` (hydrostatic profile + exact chord integral) and
`ExoLean.Iso.transitRadius` (Heng & Kitzmann 2017) for a hot-Jupiter-like atmosphere, and
checks three things numerically:

1. In the isothermal, isochemical regime, and where the optically thick limit holds
   (tau0 >> 1), the analytic formula agrees with the exact chord integral to a small fraction
   of a scale height.
2. The "inverted twin" of `Atmosphere.exists_inverted_twin` (a normal T(r) with constant X,
   versus an inverted T(r) with the compensating X'(r)) gives identical exact spectra,
   while the same inverted profile *without* compensation gives a visibly different one.
3. The isothermal twin of `Atmosphere.isothermal_twin`.

Usage: python3 scripts/numerical_check.py
"""
import numpy as np
from scipy.integrate import cumulative_trapezoid

kB = 1.380649e-23
amu = 1.66053907e-27
gammaE = 0.5772156649015329

# --- planet / atmosphere (SI) -------------------------------------------------------
R0, g, m, P0 = 7.0e7, 10.0, 2.3 * amu, 1.0e5     # 1 R_J-ish, 1 bar reference
T0, dT = 1200.0, 600.0
H0 = kB * T0 / (m * g)
L = 3 * H0                                        # width of the T transition
Rtop = R0 + 25 * H0
X0 = 1e-4

lam = np.linspace(0.3, 5.0, 60)                   # micron
sigma = 1e-27 * (lam / 0.5) ** -4.0 + 4e-26 * np.exp(-((lam - 1.4) / 0.15) ** 2)  # m^2

r = np.linspace(R0, Rtop, 6000)
logistic = lambda x: 1.0 / (1.0 + np.exp(-x))
T_normal = T0 + dT * logistic(-(r - R0) / L)
T_inverted = T0 + dT * logistic((r - R0) / L)


def pressure(T):
    """P(r) = P0 exp(-int_{R0}^r m g / (kB T))  (ExoLean.Atmosphere.pressure)."""
    return P0 * np.exp(-cumulative_trapezoid(m * g / (kB * T), r, initial=0.0))


def column(n_abs, nb=1500, ns=1500):
    """N(b) = 2 int_b^Rtop n(r) r / sqrt(r^2 - b^2) dr, via r = sqrt(b^2 + s^2)."""
    b = np.linspace(R0, Rtop, nb)[:-1]
    u = np.linspace(0.0, 1.0, ns) ** 2            # cluster nodes near the tangent point
    smax = np.sqrt(Rtop**2 - b**2)
    s = smax[:, None] * u[None, :]
    rr = np.sqrt(b[:, None] ** 2 + s**2)
    N = 2 * np.trapezoid(np.interp(rr, r, n_abs), s, axis=1)
    return b, N


def exact_spectrum(n_abs):
    """R_p^2 = R0^2 + 2 int_{R0}^{Rtop} b (1 - exp(-sigma N(b))) db (ExoLean.transitRadius)."""
    b, N = column(n_abs)
    tau = sigma[:, None] * N[None, :]
    return np.sqrt(R0**2 + 2 * np.trapezoid(b * (1 - np.exp(-tau)), b, axis=1))


def atmosphere(T, X):
    P = pressure(T)
    n = P / (kB * T)
    return P, X * n


# 1. isothermal analytic vs exact ---------------------------------------------------
T_iso = np.full_like(r, T0)
_, n_iso = atmosphere(T_iso, X0)
Rp_exact = exact_spectrum(n_iso)
kappa = X0 * sigma / m
Rp_hk = R0 + H0 * (gammaE + np.log(P0 * kappa / g * np.sqrt(2 * np.pi * R0 / H0)))
tau0 = P0 * kappa / g * np.sqrt(2 * np.pi * R0 / H0)
thick = tau0 > 10                     # regime of validity of the optically thick limit
d = (Rp_hk - Rp_exact)[thick]
print("1. Isothermal: Heng & Kitzmann (2017) vs exact chord integral")
print(f"   H = {H0/1e3:.1f} km; {thick.sum()}/{lam.size} wavelengths with tau0 > 10")
print(f"   there: |HK - exact| <= {np.abs(d).max()/H0:.3f} H")
print(f"   tau0 < 1 (E1 term no longer negligible, cf. OpenProblems target 3): "
      f"HK undershoots by up to {-(Rp_hk - Rp_exact)[tau0 < 1].min()/H0:.1f} H")

# 2. inverted twin --------------------------------------------------------------------
P_n, n_normal = atmosphere(T_normal, X0)
P_i = pressure(T_inverted)
X_comp = X0 * (T_inverted / T_normal) * (P_n / P_i)      # Atmosphere.compensation
_, n_twin = atmosphere(T_inverted, X_comp)
_, n_uncomp = atmosphere(T_inverted, X0)
Rs = 7.0e8                                               # stellar radius for depths
depth = lambda Rp: (Rp / Rs) ** 2 * 1e6                  # ppm
D_normal = depth(exact_spectrum(n_normal))
D_twin = depth(exact_spectrum(n_twin))
D_uncomp = depth(exact_spectrum(n_uncomp))
print("2. Normal T(r) + constant X  vs  inverted T(r) + compensating X'(r)")
print(f"   max |depth difference| (twin)          = {np.abs(D_twin - D_normal).max():.2e} ppm")
print(f"   max |depth difference| (uncompensated) = {np.abs(D_uncomp - D_normal).max():.1f} ppm")
print(f"   X'(r) ranges over [{X_comp.min():.2e}, {X_comp.max():.2e}] (admissible: <= 1)")

# 3. isothermal twin -------------------------------------------------------------------
c = 1.5
X_twin = c * X0 * np.exp(-(r - R0) * (1 - 1 / c) / H0)
_, n_ctwin = atmosphere(np.full_like(r, c * T0), X_twin)
print("3. Isothermal twin: T0 + constant X  vs  1.5 T0 + X' = 1.5 X exp(-(1-1/1.5)(r-R0)/H)")
print(f"   max |depth difference| = {np.abs(depth(exact_spectrum(n_ctwin)) - depth(Rp_exact)).max():.2e} ppm")
