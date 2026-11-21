#!/usr/bin/env python3
"""
Generate all 5 publication-quality vector PDF (+ 300 dpi PNG preview) figures
for the time-subordinated open quantum dynamics manuscript directly from the verified JSON/CSV datasets in `data/`.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
FIG_DIR = BASE_DIR / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

# Clean publication styling (colorblind-safe Okabe-Ito palette)
plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.labelsize": 10.5,
    "axes.titlesize": 10.5,
    "xtick.labelsize": 9.0,
    "ytick.labelsize": 9.0,
    "legend.fontsize": 8.2,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})

C_BLUE = "#0072B2"
C_ORANGE = "#E69F00"
C_VERM = "#D55E00"
C_GREEN = "#009E73"
C_PURPLE = "#CC79A7"
C_SKY = "#56B4E9"
C_DARK = "#1A1A1A"
C_GRAY = "#6C757D"


def save_fig(fig: plt.Figure, stem: str) -> None:
    pdf_path = FIG_DIR / f"{stem}.pdf"
    png_path = FIG_DIR / f"{stem}.png"
    fig.savefig(pdf_path, bbox_inches="tight")
    fig.savefig(png_path, dpi=300, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {pdf_path} and {png_path}", flush=True)


def make_fig1(df_b: pd.DataFrame, curves: dict, mu_zero_rows: list[dict] | None = None) -> None:
    """Figure 1: Exact Unclamped Phase Diagram, Buffer Asymptotics, and Pole-vs-Cut Cancellation."""
    fig, axes = plt.subplots(1, 3, figsize=(15.2, 4.4))

    # --- Panel (a): (g, mu) Phase Diagram ---
    ax = axes[0]
    sub = df_b[df_b["g"] < 1.0].copy()
    g_arr = sub["g"].to_numpy(float)
    mu_c = sub["mu_crit"].to_numpy(float)
    mu_p = sub["mu_pole"].to_numpy(float)

    g_fine = np.linspace(0.0, 0.9999, 300)
    mu_p_fine = 1.0 - np.arccos(g_fine) / np.pi

    # Append (0.0, 0.5) and (1.0, 1.0) to numerical curve for clean polygon fill
    g_poly = np.concatenate([[0.0], g_arr, [1.0]])
    muc_poly = np.concatenate([[0.5], mu_c, [1.0]])
    mup_poly = np.concatenate([[0.5], mu_p, [1.0]])

    ax.fill_between([0.0, 1.0], 0.0, 0.5, color="#E8EEF2", alpha=0.85, label=r"CM ($\mu \leq 1/2$)")
    ax.fill_between(g_fine, 0.5, mu_p_fine, color="#CFE8F3", alpha=0.85, label=r"Pole-free CP-div ($\mu \leq \mu_{\mathrm{pole}}$)")
    ax.fill_between(g_poly, mup_poly, muc_poly, color="#FDE3B8", alpha=0.90, label=r"Pole-suppressed CP-div ($\mu_{\mathrm{pole}} < \mu \leq \mu_{\mathrm{crit}}$)")
    ax.fill_between(g_poly, muc_poly, 1.0, color="#F9CFC6", alpha=0.85, label=r"Backflow ($\mathcal{N}_{\mathrm{BLP}} > 0$)")
    ax.axvspan(1.0, 1.32, color="#E5E5E5", alpha=0.85, label=r"Overdamped ($g \geq 1$: $\dot{G}<0$)")

    ax.plot(g_poly, muc_poly, "-o", color=C_VERM, lw=2.0, ms=3.2, label=r"Exact $\mu_{\mathrm{crit}}(g)$ (55-digit)")
    if mu_zero_rows:
        gz = np.array([0.0] + [float(r["g"]) for r in mu_zero_rows if r["mu_zero"] is not None] + [1.0])
        mz = np.array([0.5] + [float(r["mu_zero"]) for r in mu_zero_rows if r["mu_zero"] is not None] + [1.0])
        ax.plot(gz, mz, ":", color="#7A0177", lw=1.7, label=r"$\mu_{\mathrm{zero}}(g)$ ($G=0$ non-inv.)")
    ax.plot(g_fine, mu_p_fine, "--", color=C_DARK, lw=1.6, label=r"$\mu_{\mathrm{pole}}(g) = 1 - \frac{\arccos g}{\pi}$")
    ax.axhline(0.5, color=C_BLUE, ls=":", lw=1.3)
    ax.axvline(1.0, color=C_PURPLE, ls="-.", lw=1.6)

    ax.set_xlim(0.0, 1.30)
    ax.set_ylim(0.25, 1.02)
    ax.set_xlabel(r"Dimensionless switching rate $g$")
    ax.set_ylabel(r"Memory exponent $\mu$")
    ax.set_title(r"(a) Exact $(g,\mu)$ Phase Diagram")
    ax.legend(loc="lower right", frameon=True, framealpha=0.93, fontsize=7.2)
    ax.grid(True, alpha=0.25)

    # --- Panel (b): Buffer gap & super-exponential g -> 1^- scaling ---
    ax = axes[1]
    gap = sub["gap_mu_crit_minus_pole"].to_numpy(float)
    one_minus_muc = sub["one_minus_mu_crit"].to_numpy(float)

    ax.plot(g_arr, gap, "o-", color=C_BLUE, lw=1.9, ms=4.0, label=r"Buffer $\Delta\mu = \mu_{\mathrm{crit}} - \mu_{\mathrm{pole}}$")
    ax.set_xlabel(r"Dimensionless switching rate $g$")
    ax.set_ylabel(r"Buffer width $\mu_{\mathrm{crit}}(g) - \mu_{\mathrm{pole}}(g)$", color=C_BLUE)
    ax.tick_params(axis="y", labelcolor=C_BLUE)
    ax.set_xlim(0.0, 1.0)
    ax.set_ylim(0.0, 0.185)
    ax.grid(True, alpha=0.25)

    # Inset / secondary axis for 1 - mu_crit(g) on log scale near g -> 1^-
    ax2 = ax.twinx()
    ax2.spines["top"].set_visible(False)
    mask_hi = g_arr >= 0.50
    ax2.semilogy(g_arr[mask_hi], one_minus_muc[mask_hi], "s--", color=C_VERM, lw=1.6, ms=3.8, label=r"$1 - \mu_{\mathrm{crit}}(g)$ (log)")
    # Exact Watson-2 asymptotic ~ t1^2 / (2*g + 4*(4*g^2-1)/t1) * exp(-g * t1), t1 = (pi + arccos g)/sqrt(1-g^2)
    g_as = g_arr[g_arr >= 0.80]
    t1_as = (np.pi + np.arccos(g_as)) / np.sqrt(1.0 - g_as**2)
    asymp = (t1_as**2 / (2.0 * g_as + 4.0 * (4.0 * g_as**2 - 1.0) / t1_as)) * np.exp(-g_as * t1_as)
    ax2.semilogy(g_as, asymp, ":", color=C_DARK, lw=1.6, label=r"Watson-2 asymptotic")
    ax2.set_ylabel(r"$1 - \mu_{\mathrm{crit}}(g)$", color=C_VERM)
    ax2.tick_params(axis="y", labelcolor=C_VERM)
    ax2.set_ylim(1e-9, 1.0)
    ax.set_title(r"(b) Strict Buffer & $g \to 1^-$ Tail")
    h1, l1 = ax.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, loc="lower left", frameon=True, framealpha=0.92, fontsize=7.4)

    # --- Panel (c): Pole vs Cut competition at g=0.50 ---
    ax = axes[2]
    dc = curves["pole_vs_cut_decomp"]
    t_d = np.array(dc["t"])
    d75 = dc["mu_0.75"]
    d90 = dc["mu_0.9"]

    ax.plot(t_d, d75["dG_pole"], "--", color=C_BLUE, lw=1.4, label=r"$\dot{G}_{\mathrm{pole}}$ ($\mu=0.75$, buffer)")
    ax.plot(t_d, d75["dG_cut"], ":", color=C_SKY, lw=1.8, label=r"$\dot{G}_{\mathrm{cut}}$ ($\mu=0.75$, buffer)")
    ax.plot(t_d, d75["dG"], "-", color=C_DARK, lw=2.0, label=r"Total $\dot{G}$ ($\mu=0.75 < \mu_{\mathrm{crit}}$)")
    ax.plot(t_d, d90["dG"], "-", color=C_VERM, lw=2.0, label=r"Total $\dot{G}$ ($\mu=0.90 > \mu_{\mathrm{crit}}$)")
    ax.axhline(0.0, color="black", lw=0.8, alpha=0.6)
    ax.set_xlim(1.5, 14.0)
    ax.set_ylim(-0.045, 0.045)
    ax.set_xlabel(r"Dimensionless time $t$")
    ax.set_ylabel(r"Derivative $\dot{G}_{\mu,g}(t)$")
    ax.set_title(r"(c) Pole–Cut Competition at $g=0.50$ ($\mu_{\mathrm{pole}}=2/3$)")
    ax.legend(loc="lower right", frameon=True, framealpha=0.92, fontsize=7.5)
    ax.grid(True, alpha=0.25)

    plt.tight_layout()
    save_fig(fig, "fig1_phase_diagram_unclamped")


def make_fig2(curves: dict, summary: dict, df_land: pd.DataFrame) -> None:
    """Figure 2: Spectral Density Sign-Change, D_tr Trajectories, and Exact mu=1 BLP Law."""
    fig, axes = plt.subplots(1, 3, figsize=(15.2, 4.4))

    # --- Panel (a): Spectral density phi(r) = r * K_{mu,g}(r) ---
    ax = axes[0]
    sp = curves["spectral_density"]
    r = np.array(sp["r"])
    ax.semilogx(r, sp["phi_mu_0.4"], "-", color=C_GREEN, lw=2.0, label=r"$\mu=0.40$ (CM: $\phi > 0$)")
    ax.semilogx(r, sp["phi_mu_0.6"], "-", color=C_BLUE, lw=2.0, label=r"$\mu=0.60 \leq \mu_{\mathrm{pole}}$ (1 sign change)")
    ax.semilogx(r, sp["phi_mu_0.8"], "-", color=C_VERM, lw=1.8, label=r"$\mu=0.80 > \mu_{\mathrm{pole}}$ (resonant peak)")
    ax.axhline(0.0, color="black", lw=0.8, alpha=0.6)
    r0_60 = (-0.50 / math.cos(math.pi * 0.60)) ** (1.0 / 0.60)
    ax.axvline(r0_60, color=C_BLUE, ls=":", lw=1.2, label=rf"Root $r_0(\mu=0.60)={r0_60:.2f}$")
    ax.set_xlim(0.02, 12.0)
    ax.set_ylim(-1.02, 1.02)
    ax.set_xlabel(r"Spectral decay rate $r$")
    ax.set_ylabel(r"$\phi_{\mu,g}(r) = r\,K_{\mu,g}(r)$ ($g=0.50$)")
    ax.set_title(r"(a) Hankel Spectral Density Sign Structure")
    ax.legend(loc="lower right", frameon=True, framealpha=0.92, fontsize=7.5)
    ax.grid(True, alpha=0.25)

    # --- Panel (b): Trace Distance D_tr(t) = |G_{mu,g}(t)| ---
    ax = axes[1]
    tr = curves["trajectories"]
    t_tr = np.array(tr["t"])
    ax.plot(t_tr, tr["mu040_g050"]["D_tr"], "-", color=C_GREEN, lw=2.0, label=r"$\mu=0.40, g=0.50$ (CM)")
    ax.plot(t_tr, tr["mu075_g050"]["D_tr"], "-", color=C_BLUE, lw=2.0, label=r"$\mu=0.75, g=0.50$ (Buffer: $\mathcal{N}_{\mathrm{BLP}}=0$)")
    ax.plot(t_tr, tr["mu090_g050"]["D_tr"], "-", color=C_ORANGE, lw=2.0, label=r"$\mu=0.90, g=0.50$ (Backflow: $\mathcal{N}_{\mathrm{BLP}}>0$)")
    ax.plot(t_tr, tr["mu100_g050"]["D_tr"], "--", color=C_VERM, lw=1.7, label=r"$\mu=1.00, g=0.50$ (Exact $\mu=1$ cusps)")
    ax.plot(t_tr, tr["mu075_g125"]["D_tr"], ":", color=C_DARK, lw=2.0, label=r"$\mu=0.75, g=1.25$ (Overdamped)")
    ax.set_xlim(0.0, 14.0)
    ax.set_ylim(-0.02, 1.03)
    ax.set_xlabel(r"Dimensionless time $t$")
    ax.set_ylabel(r"Trace distance $D_{\mathrm{tr}}(t) = |G_{\mu,g}(t)|$")
    ax.set_title(r"(b) Optimal Distinguishability & Zero Cusps")
    ax.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.4)
    ax.grid(True, alpha=0.25)

    # --- Panel (c): N_BLP(mu, g) Onset + Exact mu=1 Law ---
    ax = axes[2]
    on = curves["blp_onset"]
    mu_on = np.array(on["mu"])
    cols = [C_GREEN, C_BLUE, C_ORANGE, C_VERM]
    for g_val, col in zip([0.10, 0.30, 0.50, 0.80], cols):
        ax.semilogy(mu_on, np.maximum(np.array(on[f"g_{g_val}"]), 1e-12), "o-", color=col, lw=1.8, ms=3.2, label=rf"$g = {g_val:.2f}$")

    # Mark exact mu=1 closed-form endpoints
    mu1_rows = {r["g"]: float(r["N_BLP_exact_40d"]) for r in summary["mu1_exact_verification"] if r["g"] < 1.0}
    mu1_rows[0.80] = 1.0 / (math.exp(math.pi * 0.80 / math.sqrt(1.0 - 0.80**2)) - 1.0)
    for g_val, col in zip([0.10, 0.30, 0.50, 0.80], cols):
        ax.plot(1.0, mu1_rows[g_val], "*", color=col, ms=9.5, markeredgecolor="black", markeredgewidth=0.6)
    ax.plot([], [], "*", color="gray", ms=8.5, markeredgecolor="black", label=r"Exact $\mu=1$: $(e^{\pi g/\sqrt{1-g^2}}-1)^{-1}$")

    ax.axvline(0.5, color=C_DARK, ls=":", lw=1.2)
    ax.set_xlim(0.48, 1.02)
    ax.set_ylim(1e-7, 15.0)
    ax.set_xlabel(r"Memory exponent $\mu$")
    ax.set_ylabel(r"BLP measure $\mathcal{N}_{\mathrm{BLP}}(\mu, g)$")
    ax.set_title(r"(c) Continuous Onset at $\mu_{\mathrm{crit}}(g)$ & $\mu=1$ Law")
    ax.legend(loc="upper left", frameon=True, framealpha=0.92, fontsize=7.4)
    ax.grid(True, alpha=0.25)

    plt.tight_layout()
    save_fig(fig, "fig2_spectral_and_blp_exact")


def make_fig3(hier: dict, curves: dict) -> None:
    """Figure 3: Pauli-Semigroup Subordination CP-Divisibility Breakdown."""
    fig, axes = plt.subplots(1, 2, figsize=(11.8, 4.4))

    # --- Panel (a): kappa_mu(x)/mu vs x ---
    ax = axes[0]
    kc = hier["kappa_curves"]
    x = np.array(kc["x"])
    styles = [
        ("mu_0.3", C_GRAY, ":", r"$\mu=0.30$ (monotone $< 1$)"),
        ("mu_0.5", C_GREEN, "--", r"$\mu=0.50$ (monotone $\to 1$)"),
        ("mu_0.7", C_SKY, "-", r"$\mu=0.70$ (overshoot $< 2$)"),
        ("mu_0.9", C_BLUE, "-", r"$\mu=0.90$ (overshoot $< 2$)"),
        ("mu_0.926", C_DARK, "-.", r"$\mu_* \approx 0.9261$ (threshold $= 2$)"),
        ("mu_0.95", C_ORANGE, "-", r"$\mu=0.95$ (breaks CP-div)"),
        ("mu_0.98", C_VERM, "-", r"$\mu=0.98$ (strong violation)"),
    ]
    for key, col, ls, lbl in styles:
        ax.semilogx(x, kc[key], ls=ls, color=col, lw=1.9, label=lbl)
    ax.axhline(2.0, color="crimson", ls="--", lw=1.5, label=r"CP-divisibility limit $\kappa_\mu/\mu = 2$")
    ax.axhline(1.0, color="black", ls=":", lw=0.9, alpha=0.6)
    ax.set_xlim(0.05, 16.0)
    ax.set_ylim(0.0, 3.2)
    ax.set_xlabel(r"Dimensionless argument $x = \lambda t^\mu$")
    ax.set_ylabel(r"Normalized rate $\kappa_\mu(x)/\mu$")
    ax.set_title(r"(a) Effective Rate Overshoot Above $\mu_* = 0.926058$")
    ax.legend(loc="upper left", frameon=True, framealpha=0.92, fontsize=7.6)
    ax.grid(True, alpha=0.25)

    # --- Panel (b): Explicit Counterexample Canonical Rates & Choi Eigenvalue ---
    ax = axes[1]
    pt = curves["pauli_counterexample_traj"]
    t_p = np.array(pt["t"])
    ax.plot(t_p, pt["gamma_x"], "-", color=C_VERM, lw=2.2, label=r"Canonical rate $\gamma_x(t)$ ($\gamma_x < 0$)")
    ax.plot(t_p, pt["gamma_y_z"], "--", color=C_BLUE, lw=1.9, label=r"Canonical rates $\gamma_y(t)=\gamma_z(t) > 0$")
    ax.plot(t_p, np.array(pt["step_choi_px"]) * 20.0, "-", color=C_DARK, lw=1.8, label=r"Step Choi $20 \times p_x(t, t+0.05) < 0$")
    ax.axhline(0.0, color="black", lw=1.0, alpha=0.7)
    ax.fill_between(t_p, 0.0, np.minimum(0.0, pt["gamma_x"]), color=C_VERM, alpha=0.20)

    ax.set_xlim(0.05, 3.0)
    ax.set_ylim(-0.35, 1.8)
    ax.set_xlabel(r"Time $t$ ($\mu=0.95$, parent $\gamma^{(0)}=(48,2,2)$)")
    ax.set_ylabel(r"Time-local rate $\gamma_j(t)$ / scaled Choi eig")
    ax.set_title(r"(b) P-Divisible ($\mathcal{N}_{\mathrm{BLP}}=0$) Yet Non-CP-Divisible")
    ax.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.8)
    ax.grid(True, alpha=0.25)

    plt.tight_layout()
    save_fig(fig, "fig3_pauli_subordination_counterexample")


def make_fig4(hier: dict, curves: dict) -> None:
    """Figure 4: Separation of All 6 Hierarchy Levels + Level 5 Spohn-vs-BLP Witness."""
    fig, axes = plt.subplots(1, 2, figsize=(12.2, 4.6))

    # --- Panel (a): Diagnostic Matrix across all 6 hierarchy levels ---
    ax = axes[0]
    rows = hier["hierarchy_witnesses"]
    labels = [
        "L1: Semigroup\n$e^{-t}$",
        "L2: CM\n$G_{0.40,0.20}$",
        "L3: CP-Div\n$G_{0.75,0.50}$",
        "L4a: P-Div\nEternal Pauli",
        "L4b: P-Div\nSubord. Pauli",
        "L5: Spohn\nAffine Tilt",
        "L6: CPTP\n$G_{0.90,0.50}$",
    ]
    props = ["in_Semigroup", "in_CM", "in_CP_Div", "in_P_Div", "in_Spohn_Monotone", "in_CPTP"]
    prop_labels = ["Semigroup", r"$\mathrm{CM}_{\mathrm{deph}}$", "CP-Div", "P-Div", "Spohn-Mono", "CPTP"]
    mat = np.array([[1.0 if r[p] else 0.0 for p in props] for r in rows])

    ax.imshow(mat, cmap="RdYlGn", vmin=-0.15, vmax=1.15, aspect="auto")
    for i in range(len(rows)):
        for j in range(len(props)):
            if j == 1 and (not rows[i]["in_CM"]) and rows[i].get("in_CM_componentwise", False):
                txt = "NO*"
            else:
                txt = "YES" if mat[i, j] > 0.5 else "NO"
            ax.text(j, i, txt, ha="center", va="center", fontweight="bold",
                    fontsize=8.2, color="#111111" if mat[i, j] > 0.5 else "#660000")
    ax.set_xticks(range(len(props)))
    ax.set_xticklabels(prop_labels, rotation=22, ha="right", fontsize=8.5)
    ax.set_yticks(range(len(labels)))
    ax.set_yticklabels(labels, fontsize=8.2)
    ax.set_title(r"(a) Strict 6-Level Hierarchy (*componentwise CM, multi-axis)")
    ax.set_xticks(np.arange(-0.5, len(props), 1), minor=True)
    ax.set_yticks(np.arange(-0.5, len(labels), 1), minor=True)
    ax.grid(which="minor", color="white", linestyle="-", linewidth=1.6)
    ax.tick_params(which="minor", bottom=False, left=False)

    # --- Panel (b): Level 5 Spohn-Monotone \ P-Div trajectory (zoom on t >= 1.0 tilted regime) ---
    ax = axes[1]
    l5 = curves["level5_traj"]
    t5 = np.array(l5["t"])
    D5 = np.array(l5["D_tr_opt_pair"])
    dD5 = np.array(l5["max_dD_dt_spohn"])
    m_z = t5 >= 1.0

    ax.plot(t5[m_z], D5[m_z] * 1000.0, "-", color=C_VERM, lw=2.2,
            label=r"Interior pair $10^3 D_{\mathrm{tr}}(t)$ ($\Delta D_{\mathrm{tr}}=1.14\times 10^{-4}$)")
    ax.axvline(1.0, color=C_DARK, ls=":", lw=1.4, label=r"$t=1$: tilted $K$ active ($r_{\max}=0.0935$)")
    ax.set_xlabel(r"Time $t$ ($t \geq 1$, post-contraction)")
    ax.set_ylabel(r"$10^3 \times D_{\mathrm{tr}}(\rho_1(t), \rho_2(t))$", color=C_VERM)
    ax.tick_params(axis="y", labelcolor=C_VERM)
    ax.set_xlim(1.0, 2.6)
    ax.set_ylim(3.5, 5.35)
    ax.grid(True, alpha=0.25)

    ax2 = ax.twinx()
    ax2.spines["top"].set_visible(False)
    # Include exact t=1^+ right-hand derivative from level5_details so curve starts cleanly at t=1.0
    dD_1plus = hier["level5_details"]["max_dD_dt_boundary_t1plus"]
    t_sp = np.concatenate([[1.0], t5[t5 > 1.0]])
    dD_sp = np.concatenate([[dD_1plus], dD5[t5 > 1.0]])
    ax2.plot(t_sp, dD_sp * 1e5, "--", color=C_BLUE, lw=1.9,
             label=r"$10^5 \max_{|r_0|=1} \frac{d}{dt} D(\rho(t)\|\rho_*) < 0$")
    ax2.axhline(0.0, color="black", lw=0.8, alpha=0.5)
    ax2.set_ylabel(r"$10^5 \times \max \frac{d}{dt} D(\rho(t)\|\rho_*)$", color=C_BLUE)
    ax2.tick_params(axis="y", labelcolor=C_BLUE)

    h1, l1 = ax.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, loc="lower right", frameon=True, framealpha=0.93, fontsize=7.2)
    ax.set_title(r"(b) Level 5: Global Spohn-Monotone Yet $\mathcal{N}_{\mathrm{BLP}} = 1.93\times 10^{-3}$")

    plt.tight_layout()
    save_fig(fig, "fig4_hierarchy_6levels")


def make_fig5(fl: dict) -> None:
    """Figure 5: N=1000 Unitary Friedrichs-Lee Star Hamiltonian vs Volterra E_{2-mu} vs Subordination."""
    fig, axes = plt.subplots(1, 3, figsize=(15.2, 4.4))

    # --- Panel (a): Resonant Lorentzian Bath vs mu=1 G_{1,g}(t) ---
    ax = axes[0]
    for g_key, col, g_num, g_desc in [("g_0.25", C_VERM, "0.25", "underdamped"), ("g_1.25", C_BLUE, "1.25", "overdamped")]:
        d = fl["lorentzian"][g_key]
        t = np.array(d["t"])
        ax.plot(t, d["abs_c_unitary"], "-", color=col, lw=2.2, label=rf"$N=1000$ FL unitary ($g={g_num}$, {g_desc})")
        ax.plot(t, d["abs_G1g"], ":", color=C_DARK, lw=1.6, label=rf"Exact $|G_{{1,{g_num}}}(t)|$ (err={d['max_abs_envelope_diff_vs_G1g']:.1e})")
    ax.set_xlim(0.0, 16.0)
    ax.set_ylim(-0.02, 1.03)
    ax.set_xlabel(r"Time $t$")
    ax.set_ylabel(r"Survival / coherence envelope $|c(t)|$")
    ax.set_title(r"(a) Lorentzian FL Bath ($\omega_0=25$) $\leftrightarrow$ $\mu=1$")
    ax.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.3)
    ax.grid(True, alpha=0.25)

    # --- Panel (b): One-Sided Power-Law Bath J(w) ~ w^(mu-1) exp(-w/w_c) at mu=0.50 ---
    ax = axes[1]
    d0 = fl["powerlaw"]["mu_0.5_w0_0.0"]
    d1 = fl["powerlaw"]["mu_0.5_w0_1.0"]
    t = np.array(d0["t_sub"])
    ax.plot(t, d0["abs_c_FL"], "-", color=C_VERM, lw=2.1, label=r"$N=1000$ FL ($\omega_0=0$, bound $|V_{0,0}|^2=0.61$)")
    ax.plot(t, d0["abs_c_Volterra"], "--", color=C_DARK, lw=1.4, label=rf"Continuum Volterra (diff={d0['max_abs_FL_vs_Volterra_diff']:.1e})")
    ax.plot(t, d1["abs_c_FL"], "-", color=C_ORANGE, lw=1.9, label=r"$N=1000$ FL ($\omega_0=1$, $\mathcal{N}_{\mathrm{BLP}}=0.35$)")
    ax.plot(t, d0["E_mu_subord"], "-.", color=C_GREEN, lw=1.9, label=r"Subordination $E_{0.5}(-\eta t^{0.5})$ (CM, $\mathcal{N}_{\mathrm{BLP}}=0$)")
    ax.plot(t, d0["G_mu_g03_subord"], ":", color=C_BLUE, lw=1.9, label=r"Subordination $G_{0.5, 0.3}(t)$ (CM, $\mathcal{N}_{\mathrm{BLP}}=0$)")
    ax.set_xlim(0.0, 20.0)
    ax.set_ylim(-0.02, 1.03)
    ax.set_xlabel(r"Time $t$")
    ax.set_ylabel(r"Amplitude $|c(t)|$ or $G_{0.5,g}(t)$")
    ax.set_title(r"(b) One-Sided Power-Law Bath ($\mu=0.50$): Bound State vs CM")
    ax.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.1)
    ax.grid(True, alpha=0.25)

    # --- Panel (c): Symmetric Power-Law Bath around omega_0=25 vs Volterra E_{2-mu} ---
    ax = axes[2]
    ds = fl["symmetric_powerlaw"]["mu_0.5"]
    ts = np.array(ds["t_sub"])
    ax.plot(ts, ds["rot_real_FL"], "-", color=C_BLUE, lw=2.2, label=r"$N=1000$ FL $\mathrm{Re}[e^{i\omega_0 t}c(t)]$")
    ax.plot(ts, ds["c_Volterra_sym"], "--", color=C_DARK, lw=1.5, label=rf"Real Volterra (diff={ds['max_abs_FL_rot_real_vs_Volterra_diff']:.1e})")
    ax.plot(ts, ds["E_2minusmu_broadband_sym"], ":", color=C_VERM, lw=1.9, label=r"Broadband $E_{2-\mu}=E_{1.5}(-c_{\mathrm{sym}} t^{1.5})$")
    ax.plot(ts, d0["E_mu_subord"], "-.", color=C_GREEN, lw=1.8, label=r"Inverse-$\mu$-stable $E_{0.5}(-\eta t^{0.5})$")
    ax.axhline(0.0, color="black", lw=0.8, alpha=0.6)
    ax.set_xlim(0.0, 20.0)
    ax.set_ylim(-0.55, 1.05)
    ax.set_xlabel(r"Time $t$")
    ax.set_ylabel(r"Rotating-frame coherence $\mathrm{Re}[\tilde{c}(t)]$")
    ax.set_title(r"(c) Symmetric Bath ($\mu=0.50$): $E_{2-\mu}$ Oscillations vs $E_\mu$")
    ax.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.2)
    ax.grid(True, alpha=0.25)

    plt.tight_layout()
    save_fig(fig, "fig5_friedrichs_lee_unitary")


def main():
    df_b = pd.read_csv(DATA_DIR / "phase_boundary_exact.csv")
    df_land = pd.read_csv(DATA_DIR / "blp_rhp_landscape.csv")
    with open(DATA_DIR / "phase_boundary_summary.json", encoding="utf-8") as f:
        summary = json.load(f)
    with open(DATA_DIR / "pauli_and_hierarchy_summary.json", encoding="utf-8") as f:
        hier = json.load(f)
    with open(DATA_DIR / "friedrichs_lee_comparison.json", encoding="utf-8") as f:
        fl = json.load(f)
    with open(DATA_DIR / "fig_curves.json", encoding="utf-8") as f:
        curves = json.load(f)
    mu_zero_path = DATA_DIR / "mu_zero_boundary.json"
    mu_zero_rows = json.load(open(mu_zero_path, encoding="utf-8")) if mu_zero_path.exists() else None

    make_fig1(df_b, curves, mu_zero_rows)
    make_fig2(curves, summary, df_land)
    make_fig3(hier, curves)
    make_fig4(hier, curves)
    make_fig5(fl)
    print("All 5 figures generated successfully!", flush=True)


if __name__ == "__main__":
    main()
