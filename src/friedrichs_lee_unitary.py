#!/usr/bin/env python3
"""
Microscopic N = 1000-mode Unitary Friedrichs-Lee Star Hamiltonian Comparison.

Compares exact unitary diagonalization of the (N+1)x(N+1) single-excitation
Friedrichs-Lee Hamiltonian (non-uniform Gauss-Legendre quadrature modes avoiding
uniform-grid Fourier recurrences) against:
  1. Resonant Lorentzian bath (omega_0 = 25) vs mu = 1 propagator G_{1,g}(t)
  2. Power-law bath J(w) = eta * w^(mu-1) * exp(-w/w_c) / Gamma(mu) for mu = 0.50, 0.75:
     - Exact N = 1000 unitary survival amplitude |c(t)| and bound-state weight |V_{0,0}|^2
     - Continuum Volterra integro-differential dynamics K(t) = eta * (1/w_c + i*t)^(-mu)
     - Broadband Volterra asymptotic E_{2-mu}(-c_mu t^{2-mu}) at omega_0 = 0
     - Phenomenological inverse mu-stable coherence propagator G_{mu,g}(t) and E_mu(-t^mu)
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np

from mpmath_propagator import eval_G_dG, ml_series

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def diagonalize_friedrichs_lee(omega_0: float, omegas: np.ndarray, g_couplings: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Exact diagonalization of the (N+1)x(N+1) real symmetric Friedrichs-Lee arrowhead matrix."""
    n = len(omegas)
    H = np.zeros((n + 1, n + 1), dtype=np.float64)
    H[0, 0] = omega_0
    H[0, 1:] = g_couplings
    H[1:, 0] = g_couplings
    H[np.arange(1, n + 1), np.arange(1, n + 1)] = omegas
    evals, evecs = np.linalg.eigh(H)
    weights = evecs[0, :] ** 2
    return evals, weights


def survival_amplitude_from_spec(t_grid: np.ndarray, evals: np.ndarray, weights: np.ndarray) -> np.ndarray:
    """c(t) = sum_n |V_{0,n}|^2 exp(-i E_n t)."""
    phases = np.exp(-1j * np.outer(t_grid, evals))
    return phases @ weights


def build_lorentzian_bath(N: int, omega_0: float, g_ratio: float, Delta: float = 1.0) -> tuple[np.ndarray, np.ndarray]:
    """
    Non-uniform Gauss-Legendre Cauchy-mapped discretization of
    J(w) = (1/(2*pi)) * gamma_0 * lam^2 / ((w - omega_0)^2 + lam^2) on [0, 2*omega_0]
    with lam = 2 * g_ratio * Delta and gamma_0 * lam / 2 = Delta^2.
    """
    lam = 2.0 * g_ratio * Delta
    u_max = math.atan(omega_0 / lam)
    nodes, w_gl = np.polynomial.legendre.leggauss(N)
    u = u_max * nodes
    du = u_max * w_gl
    omegas = omega_0 + lam * np.tan(u)
    g_couplings = np.sqrt((Delta ** 2 / math.pi) * du)
    return omegas, g_couplings


def build_powerlaw_bath(N: int, mu: float, eta: float, omega_c: float, omega_max: float | None = None) -> tuple[np.ndarray, np.ndarray]:
    """
    Transformed Gauss-Legendre discretization (x = w^mu) of
    J(w) = eta * w^(mu-1) * exp(-w/omega_c) / Gamma(mu) on (0, omega_max].
    Eliminates integrable w^(mu-1) singularity cleanly and avoids uniform-grid recurrences.
    """
    if omega_max is None:
        omega_max = 18.0 * omega_c
    x_max = omega_max ** mu
    nodes, w_gl = np.polynomial.legendre.leggauss(N)
    x = 0.5 * (nodes + 1.0) * x_max
    dx = 0.5 * w_gl * x_max
    omegas = x ** (1.0 / mu)
    pref = eta / (mu * math.gamma(mu))
    g_couplings = np.sqrt(pref * np.exp(-omegas / omega_c) * dx)
    return omegas, g_couplings


def build_symmetric_powerlaw_bath(N: int, omega_0: float, mu: float, eta: float, omega_c: float) -> tuple[np.ndarray, np.ndarray]:
    """
    Symmetric power-law bath J_sym(w) = eta * |w - omega_0|^(mu-1) * exp(-|w - omega_0|/omega_c) / Gamma(mu)
    supported on [0, 2*omega_0] (truncated at |delta| <= omega_0) with N/2 Gauss-Legendre modes on each side
    via transformed coordinate x = |w - omega_0|^mu.
    """
    assert N % 2 == 0
    n_half = N // 2
    x_max = omega_0 ** mu
    nodes, w_gl = np.polynomial.legendre.leggauss(n_half)
    x = 0.5 * (nodes + 1.0) * x_max
    dx = 0.5 * w_gl * x_max
    deltas = x ** (1.0 / mu)
    pref = eta / (mu * math.gamma(mu))
    g_half = np.sqrt(pref * np.exp(-deltas / omega_c) * dx)
    omegas = np.concatenate([omega_0 - deltas[::-1], omega_0 + deltas])
    g_couplings = np.concatenate([g_half[::-1], g_half])
    return omegas, g_couplings


def solve_volterra_symmetric_powerlaw(t_grid: np.ndarray, mu: float, eta: float, omega_c: float) -> np.ndarray:
    """
    Rotating-frame Volterra solver for symmetric bath around omega_0:
      K_sym(tau) = 2 * eta * Re[(1/omega_c + i*tau)^(-mu)]
    which is purely real and approaches 2*eta*cos(pi*mu/2)*tau^(-mu) as omega_c -> inf.
    """
    n = len(t_grid)
    dt = float(t_grid[1] - t_grid[0])
    taus = np.arange(n, dtype=np.float64) * dt
    K = 2.0 * eta * np.real(((1.0 / omega_c) + 1j * taus) ** (-mu))

    c = np.zeros(n, dtype=np.float64)
    c[0] = 1.0
    I_prev = 0.0
    denom = 1.0 + 0.25 * (dt ** 2) * K[0]
    for k in range(1, n):
        conv_mid = float(np.dot(K[k - 1 : 0 : -1], c[1:k])) if k > 1 else 0.0
        I_k_explicit = dt * (0.5 * K[k] * c[0] + conv_mid)
        rhs = c[k - 1] - 0.5 * dt * (I_prev + I_k_explicit)
        c[k] = rhs / denom
        I_prev = I_k_explicit + 0.5 * dt * K[0] * c[k]
    return c


def solve_volterra_powerlaw(t_grid: np.ndarray, omega_0: float, mu: float, eta: float, omega_c: float) -> np.ndarray:
    """
    Exact second-order implicit Volterra solver for
    dc/dt = -i*omega_0*c(t) - int_0^t K(t-tau) c(tau) dtau,
    where K(tau) = eta * (1/omega_c + i*tau)^(-mu).
    Note: K(0) = eta * omega_c^mu is finite for omega_c < inf!
    """
    n = len(t_grid)
    dt = float(t_grid[1] - t_grid[0])
    assert np.allclose(np.diff(t_grid), dt, rtol=1e-9), "Requires uniform t_grid"
    taus = np.arange(n, dtype=np.float64) * dt
    K = eta * ((1.0 / omega_c) + 1j * taus) ** (-mu)

    c = np.zeros(n, dtype=np.complex128)
    c[0] = 1.0 + 0.0j
    # Crank-Nicolson / trapezoidal Volterra marching:
    # (c_{k} - c_{k-1})/dt = -i w0 (c_k + c_{k-1})/2 - 0.5*(I_k + I_{k-1})
    # where I_k = dt*(0.5*K_k*c_0 + sum_{j=1}^{k-1} K_{k-j}*c_j + 0.5*K_0*c_k)
    I_prev = 0.0 + 0.0j
    denom = 1.0 + 0.5j * omega_0 * dt + 0.25 * (dt ** 2) * K[0]
    for k in range(1, n):
        # Sum over j = 1..k-1
        conv_mid = np.dot(K[k - 1 : 0 : -1], c[1:k]) if k > 1 else 0.0j
        I_k_explicit = dt * (0.5 * K[k] * c[0] + conv_mid)
        rhs = c[k - 1] * (1.0 - 0.5j * omega_0 * dt) - 0.5 * dt * (I_prev + I_k_explicit)
        c[k] = rhs / denom
        I_prev = I_k_explicit + 0.5 * dt * K[0] * c[k]
    return c


def _compute_ad_blp_metrics(t_fine: np.ndarray, evals: np.ndarray, weights: np.ndarray) -> dict:
    """Compute exact fine-grid [0, 20] equatorial coherence backflow N_BLP(|+/->)
    and true amplitude-damping optimal N_BLP^AD = max_{a in [0,1]} int_{dD/dt>0} dD/dt dt
    (Laine-Piilo-Breuer PRA 81, 062115 (2010)), where D(t) = sqrt(a^2 |c|^4 + (1-a^2)|c|^2)."""
    c_fine = survival_amplitude_from_spec(t_fine, evals, weights)
    abs_c = np.abs(c_fine)
    abs_c2 = abs_c * abs_c
    n_eq = float(np.sum(np.maximum(0.0, np.diff(abs_c))))
    n_eg = float(np.sum(np.maximum(0.0, np.diff(abs_c2))))
    best_a = 0.0 if n_eq >= n_eg else 1.0
    best_n = max(n_eq, n_eg)
    for a_val in np.linspace(0.0, 1.0, 41):
        a2 = float(a_val * a_val)
        D_t = np.sqrt(a2 * (abs_c2 ** 2) + (1.0 - a2) * abs_c2)
        nv = float(np.sum(np.maximum(0.0, np.diff(D_t))))
        if nv > best_n:
            best_n = nv
            best_a = float(a_val)
    return {
        "N_BLP_equatorial_0_to_20": n_eq,
        "N_BLP_excited_ground_0_to_20": n_eg,
        "N_BLP_AD_opt_0_to_20": best_n,
        "opt_a_AD": best_a,
    }


def run_comparison() -> dict:
    N = 1000
    t_grid = np.linspace(0.0, 20.0, 1001)  # dt = 0.02 for Volterra comparison
    t_fine = np.linspace(0.0, 20.0, 10001)  # dt = 0.002 for cusp-accurate BLP integrals

    # 1. Lorentzian bath at g = 0.25 (underdamped) and g = 1.25 (overdamped)
    lor_results = {}
    for g_val in [0.25, 1.25]:
        omegas, gs = build_lorentzian_bath(N=N, omega_0=25.0, g_ratio=g_val, Delta=1.0)
        evals, weights = diagonalize_friedrichs_lee(25.0, omegas, gs)
        c_t = survival_amplitude_from_spec(t_grid, evals, weights)
        c_rot = np.exp(1j * 25.0 * t_grid) * c_t
        blp_m = _compute_ad_blp_metrics(t_fine, evals, weights)
        # Exact mu=1 G_{1,g}(t)
        mp.mp.dps = 30
        G_exact = np.array([float(eval_G_dG(mp.mpf(str(tv)), mp.mpf(1), mp.mpf(str(g_val)))[0]) for tv in t_grid])
        max_abs_err = float(np.max(np.abs(np.abs(c_t) - np.abs(G_exact))))
        max_real_err = float(np.max(np.abs(c_rot.real - G_exact)))
        lor_results[f"g_{g_val}"] = {
            "N_modes": N,
            "omega_0": 25.0,
            "unitarity_norm": float(np.sum(weights)),
            "max_abs_envelope_diff_vs_G1g": max_abs_err,
            "max_real_rot_diff_vs_G1g": max_real_err,
            **blp_m,
            "t": t_grid.tolist()[::5],
            "abs_c_unitary": np.abs(c_t).tolist()[::5],
            "abs_G1g": np.abs(G_exact).tolist()[::5],
        }

    # 2. Power-law bath J(w) = eta * w^(mu-1) * exp(-w/omega_c) / Gamma(mu)
    pl_results = {}
    for mu_val in [0.50, 0.75]:
        for omega_0_val, eta_val, wc_val in [(0.0, 0.4, 8.0), (1.0, 0.4, 8.0)]:
            key = f"mu_{mu_val}_w0_{omega_0_val}"
            omegas, gs = build_powerlaw_bath(N=N, mu=mu_val, eta=eta_val, omega_c=wc_val)
            evals, weights = diagonalize_friedrichs_lee(omega_0_val, omegas, gs)
            c_fl = survival_amplitude_from_spec(t_grid, evals, weights)
            c_vol = solve_volterra_powerlaw(t_grid, omega_0_val, mu_val, eta_val, wc_val)
            blp_m = _compute_ad_blp_metrics(t_fine, evals, weights)

            bound_energy = float(evals[0])
            bound_weight = float(weights[0])

            mp.mp.dps = 30
            c_mu_bb = mp.mpf(str(eta_val)) * mp.exp(-1j * mp.pi * mp.mpf(str(mu_val)) / 2) * mp.gamma(1 - mp.mpf(str(mu_val)))
            t_sub = t_grid[::10]
            e_2minusmu_abs = []
            for tv in t_sub:
                if tv == 0:
                    e_2minusmu_abs.append(1.0)
                else:
                    z = -c_mu_bb * (mp.mpf(str(tv)) ** (2 - mp.mpf(str(mu_val))))
                    val = ml_series(mp.mpf(str(2 - mu_val)), mp.mpf(1), z) if abs(z) ** (1 / (2 - mu_val)) < 25 else mp.mpc(0)
                    e_2minusmu_abs.append(float(abs(val)))

            e_mu_pure = [1.0]
            G_subord = [1.0]
            for tv in t_sub[1:]:
                e_mu_pure.append(float(mp.re(ml_series(mp.mpf(str(mu_val)), mp.mpf(1), -mp.mpf(str(eta_val)) * (mp.mpf(str(tv)) ** mp.mpf(str(mu_val)))))))
                G_subord.append(float(eval_G_dG(mp.mpf(str(tv)), mp.mpf(str(mu_val)), mp.mpf("0.3"))[0]))

            max_fl_vs_vol = float(np.max(np.abs(np.abs(c_fl) - np.abs(c_vol))))
            pl_results[key] = {
                "N_modes": N,
                "mu": mu_val,
                "omega_0": omega_0_val,
                "eta": eta_val,
                "omega_c": wc_val,
                "lowest_eigenvalue_E0": bound_energy,
                "bound_state_weight": bound_weight,
                "unitarity_norm": float(np.sum(weights)),
                "max_abs_FL_vs_Volterra_diff": max_fl_vs_vol,
                "N_BLP_FL_0_to_20": blp_m["N_BLP_equatorial_0_to_20"],
                **blp_m,
                "t_sub": t_sub.tolist(),
                "abs_c_FL": np.abs(c_fl[::10]).tolist(),
                "abs_c_Volterra": np.abs(c_vol[::10]).tolist(),
                "abs_E_2minusmu_broadband": e_2minusmu_abs,
                "E_mu_subord": e_mu_pure,
                "G_mu_g03_subord": G_subord,
            }

    # 3. Symmetric power-law bath around omega_0 = 25.0 (broadband Volterra E_{2-mu} regime!)
    sym_pl_results = {}
    for mu_val in [0.50, 0.75]:
        omega_0_val, eta_val, wc_val = 25.0, 0.35, 12.0
        omegas, gs = build_symmetric_powerlaw_bath(N=N, omega_0=omega_0_val, mu=mu_val, eta=eta_val, omega_c=wc_val)
        evals, weights = diagonalize_friedrichs_lee(omega_0_val, omegas, gs)
        c_fl = survival_amplitude_from_spec(t_grid, evals, weights)
        c_rot_fl = np.exp(1j * omega_0_val * t_grid) * c_fl
        c_vol_sym = solve_volterra_symmetric_powerlaw(t_grid, mu_val, eta_val, wc_val)
        blp_m = _compute_ad_blp_metrics(t_fine, evals, weights)

        mp.mp.dps = 30
        c_sym_bb = 2 * mp.mpf(str(eta_val)) * mp.cos(mp.pi * mp.mpf(str(mu_val)) / 2) * mp.gamma(1 - mp.mpf(str(mu_val)))
        t_sub = t_grid[::10]
        e_2minusmu_sym = []
        for tv in t_sub:
            if tv == 0:
                e_2minusmu_sym.append(1.0)
            else:
                z = -c_sym_bb * (mp.mpf(str(tv)) ** (2 - mp.mpf(str(mu_val))))
                if abs(z) ** (1 / (2 - mu_val)) < 25:
                    e_2minusmu_sym.append(float(mp.re(ml_series(mp.mpf(str(2 - mu_val)), mp.mpf(1), z))))
                else:
                    e_2minusmu_sym.append(0.0)

        max_fl_vs_vol_sym = float(np.max(np.abs(c_rot_fl.real - c_vol_sym)))
        sym_pl_results[f"mu_{mu_val}"] = {
            "N_modes": N,
            "mu": mu_val,
            "omega_0": omega_0_val,
            "eta": eta_val,
            "omega_c": wc_val,
            "c_sym_broadband": float(c_sym_bb),
            "max_abs_FL_rot_real_vs_Volterra_diff": max_fl_vs_vol_sym,
            "N_BLP_FL_0_to_20": blp_m["N_BLP_equatorial_0_to_20"],
            **blp_m,
            "t_sub": t_sub.tolist(),
            "rot_real_FL": c_rot_fl.real[::10].tolist(),
            "abs_c_FL": np.abs(c_fl[::10]).tolist(),
            "c_Volterra_sym": c_vol_sym[::10].tolist(),
            "E_2minusmu_broadband_sym": e_2minusmu_sym,
        }

    out = {"lorentzian": lor_results, "powerlaw": pl_results, "symmetric_powerlaw": sym_pl_results}
    out_path = DATA_DIR / "friedrichs_lee_comparison.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, allow_nan=False)
    print(f"Saved {out_path}", flush=True)
    for k, v in lor_results.items():
        print(f"Lorentzian {k}: max_env_err={v['max_abs_envelope_diff_vs_G1g']:.3e}, N_eq={v['N_BLP_equatorial_0_to_20']:.5f}, N_AD={v['N_BLP_AD_opt_0_to_20']:.5f}")
    for k, v in pl_results.items():
        print(
            f"PowerLaw {k}: E0={v['lowest_eigenvalue_E0']:.6f}, |V00|^2={v['bound_state_weight']:.6f}, "
            f"max|FL-Volterra|={v['max_abs_FL_vs_Volterra_diff']:.3e}, N_eq={v['N_BLP_equatorial_0_to_20']:.5f}, N_AD={v['N_BLP_AD_opt_0_to_20']:.5f} (a={v['opt_a_AD']:.2f})"
        )
    for k, v in sym_pl_results.items():
        print(
            f"SymPowerLaw {k}: c_sym={v['c_sym_broadband']:.5f}, "
            f"max|FL-Volterra|={v['max_abs_FL_rot_real_vs_Volterra_diff']:.3e}, N_eq={v['N_BLP_equatorial_0_to_20']:.5f}, N_AD={v['N_BLP_AD_opt_0_to_20']:.5f}"
        )
    return out


if __name__ == "__main__":
    run_comparison()
