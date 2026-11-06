"""Generate the paper figures from scripts/numerical_check.py (run from the repo root:
python3 paper/figures/make_figures.py)."""
import runpy
import pathlib
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker

ROOT = pathlib.Path(__file__).resolve().parents[2]
ns = runpy.run_path(str(ROOT / "scripts" / "numerical_check.py"))
OUT = pathlib.Path(__file__).resolve().parent

# reference palette, light mode (slots 1-3) + text tokens
BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"
INK, INK2, GRID = "#0b0b0b", "#52514e", "#d9d8d4"
plt.rcParams.update({
    "font.family": "serif", "mathtext.fontset": "cm", "font.size": 8.5,
    "axes.edgecolor": INK2, "axes.labelcolor": INK, "xtick.color": INK2, "ytick.color": INK2,
    "axes.linewidth": 0.6, "xtick.major.width": 0.6, "ytick.major.width": 0.6,
    "axes.spines.top": False, "axes.spines.right": False, "legend.frameon": False,
    "lines.linewidth": 2.0, "savefig.bbox": "tight", "savefig.pad_inches": 0.02,
})

r, R0, H0 = ns["r"], ns["R0"], ns["H0"]
z = (r - R0) / H0

# ---------- Figure 1: the inverted twin ---------------------------------------------
fig, ax = plt.subplots(1, 3, figsize=(7.0, 2.45), gridspec_kw={"wspace": 0.42})

a = ax[0]
a.plot(ns["T_normal"], z, color=BLUE, label=r"$A$: normal")
a.plot(ns["T_inverted"], z, color=ORANGE, label=r"$A'$: inverted")
a.set_xlabel(r"$T$ [K]")
a.set_ylabel(r"altitude $(r-R_0)/H$")
a.set_title("(a) temperature", loc="left", fontsize=8.5, color=INK)
a.legend(loc="center right", fontsize=7.5)

a = ax[1]
a.plot(np.full_like(z, ns["X0"]), z, color=BLUE, label=r"$X$ (const.)")
a.plot(ns["X_comp"], z, color=ORANGE, label=r"$X'$ (twin)")
a.set_xscale("log")
a.set_xlim(None, 4e-4)
a.set_xlabel("volume mixing ratio")
a.set_title("(b) absorber abundance", loc="left", fontsize=8.5, color=INK)
a.legend(loc="lower left", fontsize=7.5)

a = ax[2]
lam = ns["lam"]
a.plot(lam, ns["D_uncomp"], color=AQUA, ls=(0, (4, 2)), label=r"inverted, $X$ fixed")
a.plot(lam, ns["D_normal"], color=BLUE, label=r"$A$")
a.plot(lam, ns["D_twin"], ls="none", marker="o", ms=3.2, mfc="white", mec=ORANGE,
       mew=1.1, label=r"$A'$ (twin)")
a.set_xscale("log")
a.set_xticks([0.3, 0.5, 1, 2, 5]); a.set_xticklabels(["0.3", "0.5", "1", "2", "5"])
a.xaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
a.set_xlabel(r"wavelength [$\mu$m]")
a.set_ylabel("transit depth [ppm]")
a.set_title("(c) exact spectrum", loc="left", fontsize=8.5, color=INK)
top = max(ns["D_uncomp"].max(), ns["D_normal"].max())
bot = ns["D_normal"].min()
a.set_ylim(bot - 0.03 * (top - bot), top + 0.62 * (top - bot))
a.legend(loc="upper left", fontsize=7.5, handlelength=1.6, borderaxespad=0.2)
for a in ax:
    a.grid(color=GRID, lw=0.4)
    a.set_axisbelow(True)
fig.savefig(OUT / "inverted_twin.pdf")

# ---------- Figure 2: analytic vs exact, against tau0 --------------------------------
fig, a = plt.subplots(figsize=(3.4, 2.4))
tau0 = ns["tau0"]
resid = (ns["Rp_hk"] - ns["Rp_exact"]) / H0
a.axvspan(tau0.min() * 0.5, 1, color=GRID, alpha=0.45, lw=0)
a.axhline(0, color=INK2, lw=0.6)
a.plot(tau0, resid, ls="none", marker="o", ms=3.5, mfc=BLUE, mec="white", mew=0.6)
a.set_xscale("log")
a.set_xlim(tau0.min() * 0.5, tau0.max() * 2)
a.set_xlabel(r"$\tau_0 = P_0\kappa/g\,\sqrt{2\pi R_0/H}$")
a.set_ylabel(r"$(R_p^{\rm HK} - R_p^{\rm exact})/H$")
a.text(0.37, 0.50, "$\\tau_0<1$:\n$E_1$ term\nmatters", transform=a.transAxes,
       fontsize=7.5, color=INK2, va="center")
a.grid(color=GRID, lw=0.4)
a.set_axisbelow(True)
fig.savefig(OUT / "hk_vs_exact.pdf")
print("figures written to", OUT)
