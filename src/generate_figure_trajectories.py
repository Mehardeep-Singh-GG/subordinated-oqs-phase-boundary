#!/usr/bin/env python3
"""
Generate exact 1:1 numerical trajectory datasets for Figures 1-5 (`data/fig_curves.json`).
Every curve plotted in the manuscript figures is stored here with zero smoothing or hacks.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

from blp_exact_helper import compute_exact_nblp_and_rhp
from mpmath_propagator import eval_G_dG, eval_G_dG_hankel_components, ml_series
from pauli_hierarchy import kappa_mu

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def K_density(r: np.ndarray, mu: float, g: float) -> np.ndarray:
    u = r ** mu
    c1 = math.cos(math.pi * mu)
    s1 = math.sin(math.pi * mu)
    c2 = math.cos(2.0 * math.pi * mu)
    u2 = u * u
    denom = u2 * u2 + 4.0 * g * g * u2 + 1.0 + 4.0 * g * u * (u2 + 1.0) * c1 + 2.0 * u2 * c2
    return 2.0 * (r ** (mu - 1.0)) * s1 * (u * c1 + g) / (math.pi * denom)


def main():
    mp.mp.dps = 35

    # 1. Pole vs Cut decomposition at g=0.50 (mu=0.75 inside buffer, mu=0.90 backflow)
    t_decomp = np.linspace(0.2, 16.0, 120)
    decomp = {"t": t_decomp.tolist()}
    for mu_val in [0.75, 0.90]:
        dG_tot, dG_p, dG_c, G_tot = [], [], [], []
        for tv in t_decomp:
            h = eval_G_dG_hankel_components(mp.mpf(str(tv)), mp.mpf(str(mu_val)), mp.mpf("0.50"))
            dG_tot.append(float(h["dG"]))
            dG_p.append(float(h["dG_pole"]))
            dG_c.append(float(h["dG_cut"]))
            G_tot.append(float(h["G"]))
        decomp[f"mu_{mu_val}"] = {
            "G": G_tot,
            "dG": dG_tot,
            "dG_pole": dG_p,
            "dG_cut": dG_c,
        }

    # 2. Spectral density phi(r) = r * K_{mu,g}(r) for g=0.50 at mu=0.40, 0.60, 0.80
    r_spec = np.geomspace(0.02, 12.0, 400)
    spec = {"r": r_spec.tolist()}
    for mu_val in [0.40, 0.60, 0.80]:
        K_v = K_density(r_spec, mu_val, 0.50)
        spec[f"K_mu_{mu_val}"] = K_v.tolist()
        spec[f"phi_mu_{mu_val}"] = (r_spec * K_v).tolist()

    # 3. Trace distance & BLP flux trajectories at g=0.50 (mu=0.40, 0.75, 0.90, 1.00) + overdamped (0.75, 1.25)
    t_traj = np.linspace(0.01, 18.0, 220)
    traj = {"t": t_traj.tolist()}
    configs = [
        (0.40, 0.50, "mu040_g050"),
        (0.75, 0.50, "mu075_g050"),
        (0.90, 0.50, "mu090_g050"),
        (1.00, 0.50, "mu100_g050"),
        (0.75, 1.25, "mu075_g125"),
    ]
    for mu_val, g_val, tag in configs:
        Gs, Dtrs, sigs = [], [], []
        for tv in t_traj:
            Gv, dGv = eval_G_dG(mp.mpf(str(tv)), mp.mpf(str(mu_val)), mp.mpf(str(g_val)))
            Gf, dGf = float(Gv), float(dGv)
            Gs.append(Gf)
            Dtrs.append(abs(Gf))
            sigs.append(dGf if Gf >= 0 else -dGf)
        traj[tag] = {"G": Gs, "D_tr": Dtrs, "sigma_BLP": sigs}

    # 4. Continuous onset of N_BLP(mu, g) vs mu for fixed g in {0.10, 0.30, 0.50, 0.80}
    mu_onset = np.linspace(0.50, 1.00, 26)
    onset = {"mu": mu_onset.tolist()}
    for g_val in [0.10, 0.30, 0.50, 0.80]:
        print(f"Computing exact BLP onset curve for g={g_val}...", flush=True)
        nblps = [compute_exact_nblp_and_rhp(float(mu_val), float(g_val), t_max=None, eps_reg=1e-3)["N_BLP"] for mu_val in mu_onset]
        onset[f"g_{g_val}"] = nblps

    # 5. Pauli counterexample trajectory for mu=0.95, gamma0=(48, 2, 2) => lam=(4, 50, 50)
    mp.mp.dps = 30
    t_pauli = np.linspace(0.05, 3.0, 120)
    mu_p = mp.mpf("0.95")
    gx_t, gy_t, px_step_t, Lamx_t, Lamy_t = [], [], [], [], []
    dt_step = mp.mpf("0.05")
    for tv in t_pauli:
        t_mp = mp.mpf(str(tv))
        kx = kappa_mu(mu_p, 4 * (t_mp ** mu_p)) / t_mp
        ky = kappa_mu(mu_p, 50 * (t_mp ** mu_p)) / t_mp
        gx_t.append(float(ky - 0.5 * kx))
        gy_t.append(float(0.5 * kx))
        # Step Choi eig on [t, t+0.05]
        Lx1 = float(mp.re(ml_series(mu_p, mp.mpf(1), -4 * (t_mp ** mu_p))))
        Ly1 = float(mp.re(ml_series(mu_p, mp.mpf(1), -50 * (t_mp ** mu_p))))
        Lx2 = float(mp.re(ml_series(mu_p, mp.mpf(1), -4 * ((t_mp + dt_step) ** mu_p))))
        Ly2 = float(mp.re(ml_series(mu_p, mp.mpf(1), -50 * ((t_mp + dt_step) ** mu_p))))
        rx, ry = Lx2 / Lx1, Ly2 / Ly1
        px_step_t.append(0.25 * (1.0 + rx - 2.0 * ry))
        Lamx_t.append(Lx1)
        Lamy_t.append(Ly1)

    pauli_traj = {
        "t": t_pauli.tolist(),
        "gamma_x": gx_t,
        "gamma_y_z": gy_t,
        "step_choi_px": px_step_t,
        "Lambda_x": Lamx_t,
        "Lambda_y_z": Lamy_t,
    }

    # 6. Level 5 trajectory (Spohn-Monotone \ P-Div) on t in [0.0, 3.5]
    r_star = np.array([0.0, 0.0, 0.80])
    s = 0.05
    K = np.array([
        [-np.log(2.0), 0.0, 1.8],
        [0.0, -np.log(2.0), 0.0],
        [0.0, 0.0, -np.log(2.5)],
    ])
    vals, vecs = np.linalg.eigh(K + K.T)
    u_opt = vecs[:, -1]
    r1 = r_star + 0.1 * u_opt
    r2 = r_star - 0.1 * u_opt
    t_l5 = np.linspace(0.0, 3.5, 141)
    D_l5, dD_l5_worst = [], []
    n_dir = 1200
    idx = np.arange(n_dir, dtype=float) + 0.5
    phi = np.arccos(1 - 2 * idx / n_dir)
    th = np.pi * (1 + 5 ** 0.5) * idx
    dirs = np.column_stack([np.sin(phi) * np.cos(th), np.sin(phi) * np.sin(th), np.cos(phi)])
    vec_star = np.array([0.0, 0.0, np.arctanh(r_star[2])])
    for tv in t_l5:
        if tv <= 1.0:
            T = (1.0 - (1.0 - s) * tv) * np.eye(3)
            c = (np.eye(3) - T) @ r_star

            def rate_u(u0: np.ndarray) -> float:
                rt = T @ u0 + c
                rn = float(np.linalg.norm(rt))
                vec_r = np.zeros(3) if rn < 1e-14 else (np.arctanh(min(rn, 1.0 - 1e-15)) / rn) * rt
                drt = -(1.0 - s) * (u0 - r_star)
                return float(np.dot(drt, vec_r - vec_star))
        else:
            T = s * expm((tv - 1.0) * K)
            c = (np.eye(3) - T) @ r_star

            def rate_u(u0: np.ndarray) -> float:
                rt = T @ u0 + c
                rn = float(np.linalg.norm(rt))
                vec_r = np.zeros(3) if rn < 1e-14 else (np.arctanh(min(rn, 1.0 - 1e-15)) / rn) * rt
                drt = K @ (rt - r_star)
                return float(np.dot(drt, vec_r - vec_star))

        rates = [rate_u(u0) for u0 in dirs]
        k_best = int(np.argmax(rates))
        max_rate = float(rates[k_best])
        opt = minimize(
            lambda ang: -rate_u(np.array([np.sin(ang[0]) * np.cos(ang[1]), np.sin(ang[0]) * np.sin(ang[1]), np.cos(ang[0])])),
            np.array([phi[k_best], th[k_best] % (2.0 * np.pi)]),
            method="Nelder-Mead",
            options={"xatol": 1e-9, "fatol": 1e-12},
        )
        max_rate = max(max_rate, float(-opt.fun))
        dD_l5_worst.append(max_rate)
        D_l5.append(float(0.5 * np.linalg.norm(T @ (r1 - r2))))

    level5_traj = {
        "t": t_l5.tolist(),
        "D_tr_opt_pair": D_l5,
        "max_dD_dt_spohn": dD_l5_worst,
    }

    out = {
        "pole_vs_cut_decomp": decomp,
        "spectral_density": spec,
        "trajectories": traj,
        "blp_onset": onset,
        "pauli_counterexample_traj": pauli_traj,
        "level5_traj": level5_traj,
    }
    out_path = DATA_DIR / "fig_curves.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
    print(f"Saved {out_path}", flush=True)


if __name__ == "__main__":
    main()
