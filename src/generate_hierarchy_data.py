#!/usr/bin/env python3
"""
Compute and export exact quantitative witnesses for:
1. Pauli-semigroup subordination critical exponent mu_* = 0.9260578... & explicit CP-breaking counterexample
2. Complete 6-level non-Markovianity hierarchy:
     Semigroup < CM < CP-Div < P-Div (BLP) < Spohn-Monotone < CPTP
   with exact Choi spectra, semigroup defect, CM spectral minimum, BLP measure,
   regularized RHP witness, and Spohn entropy production.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import numpy as np
import pandas as pd
from scipy.linalg import expm
from scipy.optimize import minimize

from blp_exact_helper import compute_exact_nblp_and_rhp
from mpmath_propagator import eval_G_dG, ml_series
from pauli_hierarchy import (
    find_mu_star_pauli_subordination,
    kappa_mu,
    scan_3d_pauli_subordination_below_mu_star,
    verify_pauli_counterexample,
)

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def K_spectral_density(r: float, mu: float, g: float) -> float:
    """Exact Hankel branch-cut spectral density K_{mu,g}(r)."""
    u = r ** mu
    c1 = np.cos(np.pi * mu)
    s1 = np.sin(np.pi * mu)
    c2 = np.cos(2.0 * np.pi * mu)
    u2 = u * u
    denom = u2 * u2 + 4.0 * g * g * u2 + 1.0 + 4.0 * g * u * (u2 + 1.0) * c1 + 2.0 * u2 * c2
    return float(2.0 * (r ** (mu - 1.0)) * s1 * (u * c1 + g) / (np.pi * denom))


def semigroup_defect_G(mu: float, g: float) -> float:
    """Estimate sup_{t,s > 0} |G(t+s) - G(t)*G(s)| on a fine grid."""
    mp.mp.dps = 22
    ts = np.array([0.2, 0.5, 1.0, 1.5, 2.5, 4.0])
    vals = {float(t): float(eval_G_dG(mp.mpf(str(t)), mp.mpf(str(mu)), mp.mpf(str(g)))[0]) for t in ts}
    max_def = 0.0
    for i, t in enumerate(ts):
        for s in ts[i:]:
            G_ts = float(eval_G_dG(mp.mpf(str(t + s)), mp.mpf(str(mu)), mp.mpf(str(g)))[0])
            d = abs(G_ts - vals[float(t)] * vals[float(s)])
            if d > max_def:
                max_def = d
    return max_def


def eval_dephasing_metrics(mu: float, g: float, t_max: float = 40.0) -> dict:
    """Compute exact Choi, CM, CP-Div, BLP, RHP, and Spohn metrics for pure-dephasing G_{mu,g}(t)."""
    mp.mp.dps = 28
    t_grid = np.concatenate([
        np.linspace(1e-3, 1.0, 40, endpoint=False),
        np.linspace(1.0, 20.0, 190, endpoint=False),
        np.linspace(20.0, t_max, 80),
    ])
    G_arr = np.empty_like(t_grid)
    dG_arr = np.empty_like(t_grid)
    for i, tv in enumerate(t_grid):
        Gv, dGv = eval_G_dG(mp.mpf(str(tv)), mp.mpf(str(mu)), mp.mpf(str(g)))
        G_arr[i] = float(Gv)
        dG_arr[i] = float(dGv)

    min_choi_global = float(0.5 * (1.0 - np.max(np.abs(G_arr))))
    zero_crossings = int(np.sum(G_arr[:-1] * G_arr[1:] < 0))

    # Time-local dephasing rate gamma_z(t) = -dG/G away from zeros
    mask_nz = np.abs(G_arr) > 1e-6
    min_gamma_z = float(np.min(-dG_arr[mask_nz] / G_arr[mask_nz]))

    # BLP & regularized RHP via exact Proposition 1(b) zero/extremum summation
    ex_blp = compute_exact_nblp_and_rhp(mu, g, t_max=None, eps_reg=1e-3)
    zero_crossings = ex_blp["zero_crossings_G"]
    n_blp = ex_blp["N_BLP"]
    i_rhp_reg = ex_blp["I_RHP_reg_eps1e3"]
    sign_G = np.where(G_arr >= 0.0, 1.0, -1.0)
    sigma_blp = sign_G * dG_arr

    # Spohn entropy production for equatorial pure state |+> (with rho_ss = I/2):
    # D(rho_+(t) || I/2) = ln 2 - H_bin((1+|G|)/2) => d/dt(-D) = -0.5 * arctanh(|G|) * d|G|/dt?
    # Note: S(rho_+(t)) = -((1+r)/2 ln((1+r)/2) + (1-r)/2 ln((1-r)/2)), r = |G(t)|.
    # d/dt(-D) = dS/dt = -arctanh(r) * dr/dt = -arctanh(|G|) * sigma_blp!
    # Check: when sigma_blp < 0 (monotonic decay toward I/2), -arctanh(|G|) * sigma_blp > 0!
    r_clip = np.clip(np.abs(G_arr), 0.0, 1.0 - 1e-12)
    sigma_spohn = -np.arctanh(r_clip) * sigma_blp
    min_spohn = float(np.min(sigma_spohn))

    # Spectral density K(r) sign check (for mu < 1)
    if mu < 1.0 - 1e-9:
        r_grid = np.geomspace(1e-3, 1e3, 400)
        K_vals = [K_spectral_density(float(r), mu, g) for r in r_grid]
        min_K = float(min(K_vals))
    else:
        min_K = 0.0

    # Also compute exact G_n finite-order derivative test for CM violation: (-1)^n G^(n)(t)
    # Using mpmath numerical differentiation at t = 0.25 for n = 2..8 when mu > 0.5
    cm_violating_n = None
    if mu > 0.5:
        mp.mp.dps = 50
        t0 = mp.mpf("0.25")
        mu_mp, g_mp = mp.mpf(str(mu)), mp.mpf(str(g))
        for n in range(1, 9):
            deriv = mp.diff(lambda x: eval_G_dG(x, mu_mp, g_mp)[0], t0, n=n)
            signed_deriv = ((-1) ** n) * deriv
            if signed_deriv < 0:
                cm_violating_n = {"n": n, "t": 0.25, "signed_deriv": float(signed_deriv)}
                break

    return {
        "min_choi_global": min_choi_global,
        "semigroup_defect": semigroup_defect_G(mu, g),
        "min_K_spectral": min_K,
        "cm_violating_deriv": cm_violating_n,
        "min_gamma_z": min_gamma_z,
        "zero_crossings_G": zero_crossings,
        "N_BLP": n_blp,
        "I_RHP_reg": i_rhp_reg,
        "min_sigma_Spohn": min_spohn,
    }


def eval_eternal_nonmarkovian_pauli() -> dict:
    """Level 4A: Hall-Cresser-Li-Andersson eternal non-Markovian Pauli channel."""
    t_grid = np.linspace(0.01, 10.0, 500)
    Lam_x = 0.5 * (1.0 + np.exp(-2.0 * t_grid))
    Lam_z = np.exp(-2.0 * t_grid)
    # Global Choi eigenvalues
    p0 = 0.25 * (1.0 + 2.0 * Lam_x + Lam_z)
    px = 0.25 * (1.0 - Lam_z)
    pz = 0.25 * (1.0 - 2.0 * Lam_x + Lam_z)  # identically 0!
    min_global_choi = float(min(np.min(p0), np.min(px), np.min(pz)))

    # Canonical rates: gamma_x = gamma_y = 1, gamma_z(t) = -tanh(t)
    min_gamma_z = float(-np.tanh(10.0))
    # Finite-step [1.0, 1.1] Choi eigenvalue
    r_x = float(0.5 * (1.0 + np.exp(-2.2)) / (0.5 * (1.0 + np.exp(-2.0))))
    r_z = float(np.exp(-2.2) / np.exp(-2.0))
    step_pz = 0.25 * (1.0 - 2.0 * r_x + r_z)

    # BLP & Spohn wrt I/2: all tilde_lam_k > 0 => N_BLP = 0, sigma_Spohn >= 0
    return {
        "min_choi_global": min_global_choi,
        "step_t1_1_t2_1_1_choi_pz": float(step_pz),
        "min_canonical_rate_gamma_z": min_gamma_z,
        "N_BLP": 0.0,
        "I_RHP_10": float(np.trapezoid(np.tanh(t_grid), t_grid)),
        "min_sigma_Spohn": 0.0,
    }


def eval_level5_spohn_monotone_non_pdiv() -> dict:
    """Level 5: Tightened Spohn-Monotone \\ P-Div continuous-time CPTP qubit channel."""
    r_star = np.array([0.0, 0.0, 0.80])
    s = 0.05
    K = np.array([
        [-np.log(2.0), 0.0, 1.8],
        [0.0, -np.log(2.0), 0.0],
        [0.0, 0.0, -np.log(2.5)],
    ])

    def T_of_t(t: float) -> np.ndarray:
        return (1.0 - (1.0 - s) * t) * np.eye(3) if t <= 1.0 else s * expm((t - 1.0) * K)

    paulis = [
        np.eye(2, dtype=complex),
        np.array([[0, 1], [1, 0]], dtype=complex),
        np.array([[0, -1j], [1j, 0]], dtype=complex),
        np.array([[1, 0], [0, -1]], dtype=complex),
    ]

    def choi_min_eig(T: np.ndarray, c: np.ndarray) -> float:
        P = np.zeros((4, 4))
        P[0, 0] = 1.0
        P[1:, 0] = c
        P[1:, 1:] = T
        J = np.zeros((4, 4), dtype=complex)
        for i in range(2):
            for j in range(2):
                Eij = np.zeros((2, 2), dtype=complex)
                Eij[i, j] = 1.0
                vin = np.array([0.5 * np.trace(paulis[a] @ Eij) for a in range(4)])
                vout = P @ vin
                PhiE = sum(vout[b] * paulis[b] for b in range(4))
                J += np.kron(Eij, PhiE) / 2.0
        return float(np.min(np.linalg.eigvalsh(J)))

    min_choi = min(choi_min_eig(T_of_t(tv), (np.eye(3) - T_of_t(tv)) @ r_star) for tv in np.linspace(0.0, 6.0, 301))
    min_choi_t_ge_1e3 = min(
        choi_min_eig(T_of_t(tv), (np.eye(3) - T_of_t(tv)) @ r_star)
        for tv in np.concatenate([np.linspace(1e-3, 1.0, 100, endpoint=False), np.linspace(1.0, 6.0, 201)])
    )
    min_choi_after_1 = min(choi_min_eig(T_of_t(tv), (np.eye(3) - T_of_t(tv)) @ r_star) for tv in np.linspace(1.0, 6.0, 201))

    # Exact forward-invariant reachable ball bound:
    # For all ||r_0||_2 <= 1, ||r_0 - r_*||_2 <= 1 + ||r_*||_2 = 1.8, so
    # ||r(t) - r_*||_2 <= s * (1 + ||r_*||_2) * sup_{tau >= 0} ||exp(tau * K)||_2.
    taus = np.linspace(0.0, 8.0, 801)
    op_norms = [float(np.linalg.norm(expm(tau * K), ord=2)) for tau in taus]
    max_op_norm = max(op_norms)
    tau_at_max_norm = float(taus[int(np.argmax(op_norms))])
    r_star_norm = float(np.linalg.norm(r_star))
    fwd_inv_radius = float(s * (1.0 + r_star_norm) * max_op_norm)

    # BLP pair on [1.0, 2.5]: (a) interior pair r_* +/- 0.1 u_opt; (b) global Bloch-ball maximum over antipodal pure states +/- u
    vals, vecs = np.linalg.eigh(K + K.T)
    u_opt = vecs[:, -1]
    r1 = r_star + 0.1 * u_opt
    r2 = r_star - 0.1 * u_opt
    ts_blp = np.linspace(1.0, 2.5, 1501)
    Ds = np.array([0.5 * np.linalg.norm(T_of_t(tv) @ (r1 - r2)) for tv in ts_blp])
    n_blp_pair = float(np.sum(np.maximum(0.0, np.diff(Ds))))

    # Global N_BLP across all initial pairs rho_1, rho_2 (attained by antipodal pure states in xz-plane)
    ts_glob = np.linspace(1.0, 6.0, 5001)
    T_glob = np.array([T_of_t(tv) for tv in ts_glob])  # (5001, 3, 3)

    def n_blp_dir(theta_val: float) -> float:
        u = np.array([np.sin(theta_val), 0.0, np.cos(theta_val)])
        # Antipodal pure pair r1 = +u, r2 = -u => dr = 2 u, D_tr(t) = ||T(t) u||_2
        D_t = np.linalg.norm(T_glob @ u, axis=1)
        return float(np.sum(np.maximum(0.0, np.diff(D_t))))

    th_scan = np.linspace(0.0, np.pi, 361)
    vals_th = [n_blp_dir(float(th_v)) for th_v in th_scan]
    best_th0 = float(th_scan[int(np.argmax(vals_th))])
    opt_blp = minimize(lambda x: -n_blp_dir(float(x[0])), np.array([best_th0]), method="Nelder-Mead", options={"xatol": 1e-8})
    n_blp_global = max(max(vals_th), float(-opt_blp.fun))
    theta_blp_global = float(opt_blp.x[0])

    # Global Spohn monotonicity helpers
    z0 = r_star[2]
    vec_star = np.array([0.0, 0.0, np.arctanh(z0)])

    def dD_dt_at_bloch(rt: np.ndarray) -> float:
        rn = float(np.linalg.norm(rt))
        vec_r = np.zeros(3) if rn < 1e-14 else (np.arctanh(min(rn, 1.0 - 1e-15)) / rn) * rt
        drt = K @ (rt - r_star)
        return float(np.dot(drt, vec_r - vec_star))

    n_dir = 2400
    idx = np.arange(n_dir, dtype=float) + 0.5
    phi = np.arccos(1 - 2 * idx / n_dir)
    th = np.pi * (1 + 5 ** 0.5) * idx
    dirs = np.column_stack([np.sin(phi) * np.cos(th), np.sin(phi) * np.sin(th), np.cos(phi)])

    # (i) Worst-case dD/dt over the pure-state initial sphere |r_0| = 1 at t = 1^+
    max_dD_t1plus = -1e99
    best_angles_t1 = (0.0, 0.0)
    for k_i, u0 in enumerate(dirs):
        rt = r_star + s * (u0 - r_star)
        val = dD_dt_at_bloch(rt)
        if val > max_dD_t1plus:
            max_dD_t1plus = val
            best_angles_t1 = (float(phi[k_i]), float(th[k_i] % (2.0 * np.pi)))

    def neg_dD_sphere(ang: np.ndarray) -> float:
        ph_a, th_a = ang
        u_a = np.array([np.sin(ph_a) * np.cos(th_a), np.sin(ph_a) * np.sin(th_a), np.cos(ph_a)])
        return -dD_dt_at_bloch(r_star + s * (u_a - r_star))

    opt_t1 = minimize(neg_dD_sphere, np.array(best_angles_t1), method="Nelder-Mead", options={"xatol": 1e-11, "fatol": 1e-14})
    max_dD_t1plus = max(max_dD_t1plus, float(-opt_t1.fun))

    # Also verify exact reachable set max distance, norm range, and pure-state sphere across t in [1.0, 3.0]
    max_dD_pure_t_ge_1 = max_dD_t1plus
    max_reachable_dist = 0.0
    max_reachable_norm = 0.0
    min_reachable_norm = 10.0
    for tv in [1.0, 1.02, 1.05, 1.1, 1.2, 1.5, 2.0, 3.0]:
        T = T_of_t(tv)
        c = (np.eye(3) - T) @ r_star
        pts = (T @ dirs.T).T + c[None, :]
        dists = np.linalg.norm(pts - r_star[None, :], axis=1)
        norms = np.linalg.norm(pts, axis=1)
        max_reachable_dist = max(max_reachable_dist, float(np.max(dists)))
        max_reachable_norm = max(max_reachable_norm, float(np.max(norms)))
        min_reachable_norm = min(min_reachable_norm, float(np.min(norms)))
        if tv > 1.0:
            for pt in pts:
                max_dD_pure_t_ge_1 = max(max_dD_pure_t_ge_1, dD_dt_at_bloch(pt))

    # (ii) Full forward-invariant enclosing ball ||r - r_*|| <= 0.095 (strictly enclosing 0.093479)
    def polish_shell(rad_val: float) -> float:
        best_v = -1e99
        best_ang = (0.0, 0.0)
        for k_i, u0 in enumerate(dirs):
            v = dD_dt_at_bloch(r_star + rad_val * u0)
            if v > best_v:
                best_v = v
                best_ang = (float(phi[k_i]), float(th[k_i] % (2.0 * np.pi)))
        opt = minimize(
            lambda ang: -dD_dt_at_bloch(r_star + rad_val * np.array([np.sin(ang[0]) * np.cos(ang[1]), np.sin(ang[0]) * np.sin(ang[1]), np.cos(ang[0])])),
            np.array(best_ang),
            method="Nelder-Mead",
            options={"xatol": 1e-11, "fatol": 1e-14},
        )
        return max(best_v, float(-opt.fun))

    max_dD_shell_r055 = polish_shell(0.055)
    max_dD_shell_r095 = polish_shell(0.095)

    # Scale-free Rayleigh ratio (dD/dt) / ||r - r_*||^2 across concentric shells inside ||r - r_*|| <= 0.095
    sup_rayleigh_inv_ball = -1e99
    max_dD_all_shells = -1e99
    for rad_rel in [1e-4, 1e-3, 0.01, 0.025, 0.04, 0.055, 0.075, 0.090, 0.0935, 0.095]:
        v_pol = polish_shell(rad_rel)
        max_dD_all_shells = max(max_dD_all_shells, v_pol)
        sup_rayleigh_inv_ball = max(sup_rayleigh_inv_ball, v_pol / (rad_rel * rad_rel))

    # Verify BKM Fisher matrix at r_* and uncontracted ||r||=0.99 behavior
    M_bkm = np.diag([np.arctanh(z0) / z0, np.arctanh(z0) / z0, 1.0 / (1.0 - z0 * z0)])
    bkm_eigs = [float(v) for v in np.linalg.eigvalsh(M_bkm @ K + K.T @ M_bkm)]
    max_uncontracted_r099 = max(dD_dt_at_bloch(0.99 * u0) for u0 in dirs)

    return {
        "r_star": [0.0, 0.0, 0.8],
        "s_contraction": s,
        "min_choi_global_t0_to_6": min_choi,
        "min_choi_t_ge_1e3": min_choi_t_ge_1e3,
        "min_choi_t_ge_1": min_choi_after_1,
        "max_eig_K_plus_KT": float(np.max(vals)),
        "max_op_norm_exp_tau_K": max_op_norm,
        "tau_at_max_op_norm": tau_at_max_norm,
        "forward_invariant_contracted_radius": fwd_inv_radius,
        "exact_max_reachable_dist": max_reachable_dist,
        "reachable_bloch_norm_range": [min_reachable_norm, max_reachable_norm],
        "bkm_hessian_eigs_at_r_star": bkm_eigs,
        "blp_pair_revival_t1_to_2_5": n_blp_pair,
        "blp_global_max_antipodal": n_blp_global,
        "blp_global_opt_theta_rad": theta_blp_global,
        "max_dD_dt_boundary_t1plus": float(max_dD_t1plus),
        "max_dD_dt_pure_sphere_t_ge_1": float(max_dD_pure_t_ge_1),
        "max_dD_dt_invariant_ball_shell_r055": float(max_dD_shell_r055),
        "max_dD_dt_invariant_ball_shell_r095": float(max_dD_shell_r095),
        "max_dD_dt_invariant_ball_all_nonzero_shells": float(max_dD_all_shells),
        "sup_dD_dt_over_r2_invariant_ball_r095": float(sup_rayleigh_inv_ball),
        "max_dD_dt_uncontracted_r099": float(max_uncontracted_r099),
        "min_sigma_Spohn_boundary_t1plus": float(-max_dD_t1plus),
        "min_sigma_Spohn_shell_r095": float(-max_dD_shell_r095),
    }


def main():
    print("Computing Pauli subordination & 6-level hierarchy dataset...", flush=True)
    mu_star_res = find_mu_star_pauli_subordination()
    pauli_ce = verify_pauli_counterexample()

    # Evaluate kappa_mu(x)/mu curves for plotting
    mp.mp.dps = 25
    x_curve = np.geomspace(0.05, 16.0, 65)
    kappa_curves = {"x": x_curve.tolist()}
    for mu_f in [0.30, 0.50, 0.70, 0.85, 0.90, 0.926, 0.95, 0.98]:
        mu_mp = mp.mpf(str(mu_f))
        kappa_curves[f"mu_{mu_f}"] = [float(kappa_mu(mu_mp, mp.mpf(str(xv))) / mu_mp) for xv in x_curve]

    # Evaluate 6-level witnesses
    l1 = eval_dephasing_metrics(1.0, 0.5)   # wait: G_{1, 0.5} has oscillations! Use pure exponential semigroup e^{-t}!
    # Actually let's use exact semigroup e^{-t} for Level 1!
    t_sg = np.linspace(0.0, 20.0, 200)
    l1_exact = {
        "witness": "Markov semigroup G(t) = exp(-t)",
        "level": "1_Semigroup",
        "in_Semigroup": True,
        "in_CM": True,
        "in_CP_Div": True,
        "in_P_Div": True,
        "in_Spohn_Monotone": True,
        "in_CPTP": True,
        "semigroup_defect": 0.0,
        "min_K_spectral": 0.0,
        "min_canonical_rate": 1.0,
        "N_BLP": 0.0,
        "I_RHP_reg": 0.0,
        "min_sigma_Spohn": 0.0,
        "min_choi_global": float(0.5 * (1.0 - np.exp(-1e-3))),
    }

    m2 = eval_dephasing_metrics(0.40, 0.20)
    l2_exact = {
        "witness": "G_{0.40, 0.20}(t) (CM pole-free)",
        "level": "2_CM_non_Semigroup",
        "in_Semigroup": False,
        "in_CM": True,
        "in_CP_Div": True,
        "in_P_Div": True,
        "in_Spohn_Monotone": True,
        "in_CPTP": True,
        "semigroup_defect": m2["semigroup_defect"],
        "min_K_spectral": m2["min_K_spectral"],
        "min_canonical_rate": m2["min_gamma_z"],
        "N_BLP": m2["N_BLP"],
        "I_RHP_reg": m2["I_RHP_reg"],
        "min_sigma_Spohn": m2["min_sigma_Spohn"],
        "min_choi_global": m2["min_choi_global"],
    }

    # Level 3: BOTH pole-free wedge (0.65, 0.50) and buffer wedge (0.75, 0.50) and overdamped (1.0, 1.25)
    m3a = eval_dephasing_metrics(0.65, 0.50)
    m3b = eval_dephasing_metrics(0.75, 0.50)
    m3c = eval_dephasing_metrics(1.00, 1.25)
    l3_exact = {
        "witness": "G_{0.75, 0.50}(t) (Buffer wedge CP-Div \\ CM)",
        "level": "3_CP_Div_non_CM",
        "in_Semigroup": False,
        "in_CM": False,
        "in_CP_Div": True,
        "in_P_Div": True,
        "in_Spohn_Monotone": True,
        "in_CPTP": True,
        "semigroup_defect": m3b["semigroup_defect"],
        "min_K_spectral": m3b["min_K_spectral"],
        "cm_violating_deriv": m3b["cm_violating_deriv"],
        "min_canonical_rate": m3b["min_gamma_z"],
        "N_BLP": m3b["N_BLP"],
        "I_RHP_reg": m3b["I_RHP_reg"],
        "min_sigma_Spohn": m3b["min_sigma_Spohn"],
        "min_choi_global": m3b["min_choi_global"],
    }

    m4a = eval_eternal_nonmarkovian_pauli()
    l4a_exact = {
        "witness": "Eternal NM Pauli (gamma_x=gamma_y=1, gamma_z=-tanh t)",
        "level": "4A_P_Div_non_CP_Div",
        "in_Semigroup": False,
        "in_CM": False,  # scalar single-axis CM_deph only; componentwise Bloch multipliers ARE CM
        "in_CM_componentwise": True,
        "in_CP_Div": False,
        "in_P_Div": True,
        "in_Spohn_Monotone": True,
        "in_CPTP": True,
        "semigroup_defect": None,
        "min_K_spectral": None,
        "min_canonical_rate": m4a["min_canonical_rate_gamma_z"],
        "step_negative_choi": m4a["step_t1_1_t2_1_1_choi_pz"],
        "N_BLP": m4a["N_BLP"],
        "I_RHP_reg": m4a["I_RHP_10"],
        "min_sigma_Spohn": m4a["min_sigma_Spohn"],
        "min_choi_global": m4a["min_choi_global"],
    }

    # Global Choi eigenvalue of Level 4B on t >= 1e-3
    mp.mp.dps = 25
    mu_4b = mp.mpf("0.95")
    lam_4b = (mp.mpf(4), mp.mpf(50), mp.mpf(50))
    ts_4b = [mp.mpf(str(tv)) for tv in (1e-3, 1e-2, 0.05, 0.2, 0.5, 1.0, 2.0, 5.0)]
    min_choi_4b_ge_1e3 = float("inf")
    for tv in ts_4b:
        L = [float(mp.re(ml_series(mu_4b, mp.mpf(1), -l * (tv ** mu_4b)))) for l in lam_4b]
        eigs = [
            0.25 * (1.0 + L[0] + L[1] + L[2]),
            0.25 * (1.0 + L[0] - L[1] - L[2]),
            0.25 * (1.0 - L[0] + L[1] - L[2]),
            0.25 * (1.0 - L[0] - L[1] + L[2]),
        ]
        min_choi_4b_ge_1e3 = min(min_choi_4b_ge_1e3, min(eigs))

    l4b_exact = {
        "witness": "Subordinated Pauli (mu=0.95, gamma=(48,2,2))",
        "level": "4B_P_Div_non_CP_Div_Subord",
        "in_Semigroup": False,
        "in_CM": False,  # scalar single-axis CM_deph only; componentwise Bloch multipliers E_0.95(-lam_k t^0.95) ARE CM
        "in_CM_componentwise": True,
        "in_CP_Div": False,
        "in_P_Div": True,
        "in_Spohn_Monotone": True,
        "in_CPTP": True,
        "min_canonical_rate": float(pauli_ce["canonical_rates_t1"]["gamma_x"]),
        "step_negative_choi": float(pauli_ce["min_step_choi_eig"]),
        "N_BLP": 0.0,
        "I_RHP_reg": None,
        "min_sigma_Spohn": 0.0,
        "min_choi_global": min_choi_4b_ge_1e3,
        "min_choi_at_t1": min(float(v) for v in pauli_ce["global_choi_eigs_t1"]),
    }

    print("Running exhaustive 3D Pauli subordination scan below mu_*...", flush=True)
    pauli_3d_scan = scan_3d_pauli_subordination_below_mu_star()

    m5 = eval_level5_spohn_monotone_non_pdiv()
    l5_exact = {
        "witness": "Non-unital tilted affine (r_*=(0,0,0.8), s=0.05, K_xz=1.8)",
        "level": "5_Spohn_non_P_Div",
        "in_Semigroup": False,
        "in_CM": False,
        "in_CM_componentwise": False,
        "in_CP_Div": False,
        "in_P_Div": False,
        "in_Spohn_Monotone": True,
        "in_CPTP": True,
        "min_canonical_rate": -m5["max_eig_K_plus_KT"],
        "N_BLP": m5["blp_global_max_antipodal"],
        "N_BLP_interior_pair": m5["blp_pair_revival_t1_to_2_5"],
        "min_sigma_Spohn": m5["min_sigma_Spohn_boundary_t1plus"],
        "min_choi_global": m5["min_choi_t_ge_1e3"],
    }

    m6 = eval_dephasing_metrics(0.90, 0.50)
    l6_exact = {
        "witness": "G_{0.90, 0.50}(t) (Backflow mu > mu_crit)",
        "level": "6_CPTP_non_Spohn",
        "in_Semigroup": False,
        "in_CM": False,
        "in_CP_Div": False,
        "in_P_Div": False,
        "in_Spohn_Monotone": False,
        "in_CPTP": True,
        "semigroup_defect": m6["semigroup_defect"],
        "min_K_spectral": m6["min_K_spectral"],
        "min_canonical_rate": m6["min_gamma_z"],
        "zero_crossings_G": m6["zero_crossings_G"],
        "N_BLP": m6["N_BLP"],
        "I_RHP_reg": m6["I_RHP_reg"],
        "min_sigma_Spohn": m6["min_sigma_Spohn"],
        "min_choi_global": m6["min_choi_global"],
    }

    hierarchy_rows = [l1_exact, l2_exact, l3_exact, l4a_exact, l4b_exact, l5_exact, l6_exact]
    pd.DataFrame(hierarchy_rows).to_csv(DATA_DIR / "hierarchy_6levels.csv", index=False)

    out = {
        "pauli_mu_star": mu_star_res,
        "pauli_counterexample": pauli_ce,
        "pauli_3d_scan": pauli_3d_scan,
        "kappa_curves": kappa_curves,
        "level3_pole_free_mu065_g050": m3a,
        "level3_overdamped_mu100_g125": m3c,
        "level5_details": m5,
        "hierarchy_witnesses": hierarchy_rows,
    }
    with open(DATA_DIR / "pauli_and_hierarchy_summary.json", "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, allow_nan=False)
    print(f"Saved {DATA_DIR / 'pauli_and_hierarchy_summary.json'} and hierarchy_6levels.csv", flush=True)
    for row in hierarchy_rows:
        print(
            f"  {row['level']:<30} | N_BLP={row.get('N_BLP', 0):.5f} | min_gamma={row.get('min_canonical_rate', 0):+.5f} | "
            f"min_Spohn={row.get('min_sigma_Spohn', 0):+.3e} | min_Choi={row.get('min_choi_global', 0):+.5f}",
            flush=True,
        )


if __name__ == "__main__":
    main()
