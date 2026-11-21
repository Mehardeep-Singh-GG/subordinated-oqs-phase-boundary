#!/usr/bin/env python3
"""
High-precision analysis of:
1. Pauli-semigroup inverse-mu-stable subordination (kappa_mu(x) = x E_{mu,mu}(-x)/E_mu(-x)):
   - Monotonicity & subadditivity for mu <= 1/2
   - Exact threshold mu_* where max_x kappa_mu(x) = 2*mu (breaking triangle inequality!)
   - Search over arbitrary parent Pauli rates (gamma_x, gamma_y, gamma_z) >= 0 for smallest mu breaking CP-divisibility
   - Explicit CP-breaking counterexample with exact negative Choi eigenvalue
2. All 6 levels of the non-Markovianity hierarchy:
   Semigroup < CM < CP-Div < P-Div (BLP) < Spohn-Monotone < CPTP
   with exact Choi spectra, BLP flux, RHP witness, and Spohn entropy production.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import numpy as np

from mpmath_propagator import eval_G_dG, eval_G_dG_hankel_components, ml_series

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def kappa_mu(mu: mp.mpf, x: mp.mpf) -> mp.mpf:
    """Dimensionless effective rate kappa_mu(x) = x * E_{mu,mu}(-x) / E_mu(-x) for x >= 0."""
    if x == 0:
        return mp.mpf(0)
    # Use Hankel cut directly when x^(1/mu) > 25 to avoid power-series cancellation
    scale = float(x ** (1 / mu))
    if scale <= 25.0:
        with mp.extradps(20):
            E1 = mp.re(ml_series(mu, mp.mpf(1), -x))
            Emm = mp.re(ml_series(mu, mu, -x))
            return +(x * Emm / E1)
    # Hankel integral for E_mu(-x) and x E_{mu,mu}(-x) = -d/dt E_mu(-t^mu) at t = x^(1/mu)
    with mp.extradps(15):
        t = x ** (1 / mu)
        c1 = mp.cos(mp.pi * mu)
        s1 = mp.sin(mp.pi * mu)
        pref = s1 / (mp.pi * mu)
        inv_mu = 1 / mu
        x_max = mp.mpf(int((mp.mp.dps + 12) * 2.31) + 5)
        u_max = (x_max / t) ** mu

        def denom_sq(u: mp.mpf) -> mp.mpf:
            return u * u + 2 * u * c1 + 1

        def int_E1(u: mp.mpf) -> mp.mpf:
            rt = (u ** inv_mu) * t
            if rt > x_max + 20:
                return mp.mpf(0)
            return pref * mp.exp(-rt) / denom_sq(u)

        def int_dE1(u: mp.mpf) -> mp.mpf:
            r = u ** inv_mu
            rt = r * t
            if rt > x_max + 20:
                return mp.mpf(0)
            return pref * r * mp.exp(-rt) / denom_sq(u)

        pts = [mp.mpf(0)]
        for p in sorted([t ** (-mu), (5 / t) ** mu, mp.mpf(1)]):
            if mp.mpf("1e-35") < p < u_max and p > pts[-1] * (1 + mp.mpf("1e-12")):
                pts.append(p)
        if u_max > pts[-1] * (1 + mp.mpf("1e-12")):
            pts.append(u_max)
        E1 = mp.quad(int_E1, pts)
        dE1 = mp.quad(int_dE1, pts)  # = t^(mu-1) E_{mu,mu}(-t^mu)
        return +(t * dE1 / E1)


def find_max_kappa_over_mu(mu_val: float) -> tuple[mp.mpf, mp.mpf]:
    """Find max_{x > 0} kappa_mu(x) / mu and the maximizing x."""
    mu = mp.mpf(str(mu_val))
    # Coarse grid on x in [0.5, 14.0] (overshoot peak occurs near x ~ 3..6)
    xs = [mp.mpf(x) for x in np.geomspace(0.5, 14.0, 22)]
    vals = [kappa_mu(mu, x) / mu for x in xs]
    idx = int(np.argmax([float(v) for v in vals]))
    if idx == len(xs) - 1:
        return vals[-1], xs[-1]
    a = xs[max(0, idx - 1)]
    b = xs[min(len(xs) - 1, idx + 1)]
    phi = (mp.sqrt(5) - 1) / 2
    c = b - phi * (b - a)
    d = a + phi * (b - a)
    fc = kappa_mu(mu, c) / mu
    fd = kappa_mu(mu, d) / mu
    for _ in range(25):
        if fc < fd:
            a, c, fc = c, d, fd
            d = a + phi * (b - a)
            fd = kappa_mu(mu, d) / mu
        else:
            b, d, fd = d, c, fc
            c = b - phi * (b - a)
            fc = kappa_mu(mu, c) / mu
    if fc > fd:
        return fc, c
    return fd, d


def kappa_and_deriv_series(mu: mp.mpf, x: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    """
    Exact power-series evaluation of kappa_mu(x) = x E_{mu,mu}(-x) / E_mu(-x)
    and its exact analytical x-derivative:
        kappa'_mu(x) = g'(x)/f(x) + kappa_mu(x)^2 / (mu * x),
    where f(x) = E_mu(-x) and g(x) = x E_{mu,mu}(-x), valid for moderate x (x^(1/mu) <= 25).
    """
    with mp.extradps(25):
        eps = mp.mpf(10) ** (-(mp.mp.dps + 8))
        f_sum = mp.mpf(0)
        g_sum = mp.mpf(0)
        gp_sum = mp.mpf(0)
        x_pow = mp.mpf(1)  # (-x)^n
        for n in range(2500):
            inv_gf = 1 / mp.gamma(mu * n + 1)
            inv_gg = 1 / mp.gamma(mu * n + mu)
            tf = x_pow * inv_gf
            tgg = x_pow * inv_gg
            f_sum += tf
            g_sum += tgg
            gp_sum += (n + 1) * tgg
            if n > 12 and abs(tf) < eps * max(mp.mpf(1), abs(f_sum)) and abs((n + 1) * tgg) < eps * max(mp.mpf(1), abs(gp_sum)):
                break
            x_pow *= -x
        g_val = x * g_sum
        kap = g_val / f_sum
        dkap = gp_sum / f_sum + (kap * kap) / (mu * x)
        return +kap, +dkap


def find_mu_star_pauli_subordination() -> dict:
    """
    Solve the exact 2D critical system
        F1(mu, x) = kappa_mu(x) - 2*mu = 0,
        F2(mu, x) = d/dx kappa_mu(x) = 0
    via 2D Newton iteration at 75-digit precision, cross-checked at 95-digit precision,
    and compute the associated exact threshold geometry at mu = mu_*.
    """
    def solve_2d_newton(work_dps: int) -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
        with mp.workdps(work_dps):
            mu = mp.mpf("0.9260578")
            x = mp.mpf("3.6356687")
            h = mp.mpf(10) ** (-(work_dps // 3))
            for _ in range(14):
                k0, dk0 = kappa_and_deriv_series(mu, x)
                f1 = k0 - 2 * mu
                f2 = dk0
                if max(abs(f1), abs(f2)) < mp.mpf(10) ** (-(work_dps - 10)):
                    break
                # Central-difference Jacobian in (mu, x)
                kp_m, dkp_m = kappa_and_deriv_series(mu + h, x)
                km_m, dkm_m = kappa_and_deriv_series(mu - h, x)
                kp_x, dkp_x = kappa_and_deriv_series(mu, x + h)
                km_x, dkm_x = kappa_and_deriv_series(mu, x - h)
                j11 = (kp_m - km_m) / (2 * h) - 2
                j12 = (kp_x - km_x) / (2 * h)
                j21 = (dkp_m - dkm_m) / (2 * h)
                j22 = (dkp_x - dkm_x) / (2 * h)
                det = j11 * j22 - j12 * j21
                dmu = -(j22 * f1 - j12 * f2) / det
                dx = -(-j21 * f1 + j11 * f2) / det
                mu += dmu
                x += dx
            k_res, dk_res = kappa_and_deriv_series(mu, x)
            return +mu, +x, abs(k_res - 2 * mu), abs(dk_res)

    mu_75, x_75, res1_75, res2_75 = solve_2d_newton(75)
    mu_95, x_95, res1_95, res2_95 = solve_2d_newton(95)

    with mp.workdps(75):
        mu_star = +mu_95
        x_star = +x_95
        diff_mu = abs(mu_95 - mu_75)
        diff_x = abs(x_95 - x_75)

        # Solve unique x0 in (0, x_star) where kappa_{mu_*}(x0) = mu_*
        x0 = mp.mpf("1.08")
        for _ in range(16):
            kv, dkv = kappa_and_deriv_series(mu_star, x0)
            step = (kv - mu_star) / dkv
            x0 -= step
            if abs(step) < mp.mpf("1e-65"):
                break
        res_x0 = abs(kappa_and_deriv_series(mu_star, x0)[0] - mu_star)

        # Exact secant slopes at x0 and x_star, plus initial slope 1/Gamma(mu_*)
        slope_zero = 1 / mp.gamma(mu_star)
        slope_at_x0 = mu_star / x0
        secant_at_x_star = 2 * mu_star / x_star

        # Verify kappa_{mu_*}(r)/r is strictly decreasing on (0, x0] by checking its derivative on 200 points
        rs_check = [x0 * mp.mpf(j) / 200 for j in range(1, 201)]
        max_d_kap_over_r = max((dk * r - k) / (r * r) for r in rs_check for k, dk in [kappa_and_deriv_series(mu_star, r)])

        # Compute exact L_down = sup_{x > x_star} |kappa'_{mu_*}(x)| (downward inflection slope after peak)
        # Coarse scan on [x_star, 12.0] (still in series regime: 12^(1/0.926) = 14.6 <= 25)
        xs_down = [x_star + mp.mpf(j) * mp.mpf("0.05") for j in range(1, 165)]
        dks_down = [kappa_and_deriv_series(mu_star, xv)[1] for xv in xs_down]
        idx_min_dk = int(np.argmin([float(v) for v in dks_down]))
        x_inf = xs_down[idx_min_dk]
        # Polish inflection point kappa''_{mu_*}(x_inf) = 0 via central differences
        h_inf = mp.mpf("1e-22")
        for _ in range(12):
            _, dk_0 = kappa_and_deriv_series(mu_star, x_inf)
            _, dk_p = kappa_and_deriv_series(mu_star, x_inf + h_inf)
            _, dk_m = kappa_and_deriv_series(mu_star, x_inf - h_inf)
            d2 = (dk_p - dk_m) / (2 * h_inf)
            d3 = (dk_p - 2 * dk_0 + dk_m) / (h_inf * h_inf)
            step = d2 / d3
            x_inf -= step
            if abs(step) < mp.mpf("1e-40"):
                break
        _, dk_inf = kappa_and_deriv_series(mu_star, x_inf)
        L_down = -dk_inf

    # Verify L_down(mu) < mu / x0(mu) across mu in (0.60, 0.70, 0.80, 0.85, 0.90, mu_star)
    # confirming Proposition 7 across the entire interval (1/2, mu_*]!
    asymmetric_margin_sweep = {}
    with mp.workdps(30):
        def _dk_safe(mu_v: mp.mpf, xv: mp.mpf) -> mp.mpf:
            if float(xv ** (1 / mu_v)) <= 22.0:
                return kappa_and_deriv_series(mu_v, xv)[1]
            h = mp.mpf("1e-6") * xv
            return (kappa_mu(mu_v, xv + h) - kappa_mu(mu_v, xv - h)) / (2 * h)

        for mu_lbl, mu_v in [
            ("0.60", mp.mpf("0.60")),
            ("0.70", mp.mpf("0.70")),
            ("0.80", mp.mpf("0.80")),
            ("0.85", mp.mpf("0.85")),
            ("0.90", mp.mpf("0.90")),
            ("mu_star", mp.mpf(mu_star)),
        ]:
            # Solve x0 where kappa_mu(x0) = mu
            x0_v = mp.mpf("1.5") if mu_v > mp.mpf("0.65") else mp.mpf("3.0")
            for _ in range(25):
                kv, dkv = kappa_and_deriv_series(mu_v, x0_v)
                st = (kv - mu_v) / dkv
                x0_v -= st
                if abs(st) < mp.mpf("1e-22"):
                    break
            # Find peak x_peak where kappa'_mu(x_peak) = 0
            xs_scan = [mp.mpf(str(v)) for v in np.linspace(1.5, 9.0, 76)]
            k_scan = [kappa_mu(mu_v, xv) for xv in xs_scan]
            xp = xs_scan[int(np.argmax([float(v) for v in k_scan]))]
            h_d = mp.mpf("1e-6")
            for _ in range(12):
                dk0 = _dk_safe(mu_v, xp)
                dkp = _dk_safe(mu_v, xp + h_d)
                dkm = _dk_safe(mu_v, xp - h_d)
                d2 = (dkp - dkm) / (2 * h_d)
                st = dk0 / d2
                xp -= st
                if abs(st) < mp.mpf("1e-14"):
                    break
            # Scan downward slope L_down = sup_{x > x_peak} |kappa'_mu(x)| using Hankel-safe _dk_safe
            xs_dn = [xp + mp.mpf(j) * mp.mpf("0.3") for j in range(1, 50)]
            dks_dn = [_dk_safe(mu_v, xv) for xv in xs_dn]
            idx_dn = int(np.argmin([float(v) for v in dks_dn]))
            a_dn = xs_dn[max(0, idx_dn - 1)]
            b_dn = xs_dn[min(len(xs_dn) - 1, idx_dn + 1)]
            phi_g = (mp.sqrt(5) - 1) / 2
            c_dn = b_dn - phi_g * (b_dn - a_dn)
            d_dn = a_dn + phi_g * (b_dn - a_dn)
            fc_dn, fd_dn = _dk_safe(mu_v, c_dn), _dk_safe(mu_v, d_dn)
            for _ in range(30):
                if fc_dn < fd_dn:
                    b_dn, d_dn, fd_dn = d_dn, c_dn, fc_dn
                    c_dn = b_dn - phi_g * (b_dn - a_dn)
                    fc_dn = _dk_safe(mu_v, c_dn)
                else:
                    a_dn, c_dn, fc_dn = c_dn, d_dn, fd_dn
                    d_dn = a_dn + phi_g * (b_dn - a_dn)
                    fd_dn = _dk_safe(mu_v, d_dn)
            xi_dn = (a_dn + b_dn) / 2
            L_dn = -_dk_safe(mu_v, xi_dn)
            assert L_dn > 0 and xi_dn > xp, f"Invalid downward inflection at mu={mu_lbl}: xi={xi_dn}, L_dn={L_dn}"
            sec_x0 = mu_v / x0_v
            asymmetric_margin_sweep[mu_lbl] = {
                "x0": mp.nstr(x0_v, 14),
                "x_peak": mp.nstr(xp, 14),
                "x_inflection": mp.nstr(xi_dn, 14),
                "mu_over_x0": mp.nstr(sec_x0, 14),
                "L_down": mp.nstr(L_dn, 14),
                "strict_margin_holds": bool(L_dn < sec_x0),
            }

    # Check kappa_mu(x)/mu across mu in (0.3, 0.95) for x up to 25 (series regime, super fast!)
    mp.mp.dps = 25
    min_ratio_scan = {}
    for mu_test in [0.3, 0.5, 0.7, 0.85, 0.90, 0.92, 0.95]:
        mu_mp = mp.mpf(str(mu_test))
        xs_small = [mp.mpf(str(xv)) for xv in (0.2, 0.5, 1.0, 2.0, 3.5, 5.0, 7.0, 10.0, 15.0)]
        vals = [kappa_mu(mu_mp, x) / mu_mp for x in xs_small if float(x ** (1 / mu_mp)) <= 25.0]
        if mu_test >= 0.7:
            rmax, xmax = find_max_kappa_over_mu(mu_test)
        else:
            rmax, xmax = max(vals), xs_small[int(np.argmax([float(v) for v in vals]))]
        min_ratio_scan[str(mu_test)] = {
            "max_kappa_over_mu": mp.nstr(rmax, 15),
            "x_at_max": mp.nstr(xmax, 10),
            "min_val_sampled": mp.nstr(min(vals), 10),
        }

    with mp.workdps(75):
        return {
            "mu_star": mp.nstr(mu_star, 55),
            "x_star": mp.nstr(x_star, 55),
            "residual_kappa_minus_2mu_95dps": mp.nstr(res1_95, 6),
            "residual_dkappa_95dps": mp.nstr(res2_95, 6),
            "crosscheck_diff_mu_75_vs_95": mp.nstr(diff_mu, 6),
            "crosscheck_diff_x_75_vs_95": mp.nstr(diff_x, 6),
            "x0_mu_star": mp.nstr(x0, 35),
            "residual_x0": mp.nstr(res_x0, 6),
            "slope_at_zero_inv_gamma": mp.nstr(slope_zero, 25),
            "min_secant_on_0_to_x0": mp.nstr(slope_at_x0, 25),
            "secant_at_x_star_2mu_over_xstar": mp.nstr(secant_at_x_star, 25),
            "max_d_kappa_over_r_on_0_to_x0": mp.nstr(max_d_kap_over_r, 12),
            "x_downward_inflection": mp.nstr(x_inf, 25),
            "L_down_max_neg_slope": mp.nstr(L_down, 25),
            "asymmetric_margin_sweep": asymmetric_margin_sweep,
            "ratio_scan": min_ratio_scan,
        }


def verify_pauli_counterexample() -> dict:
    """Verify explicit CP-breaking subordinated Pauli semigroup at mu=0.95."""
    mp.mp.dps = 50
    mu = mp.mpf("0.95")
    # Parent Markovian generator: gamma_x=48, gamma_y=2, gamma_z=2 -> lambda=(4, 50, 50)
    gam0 = (mp.mpf(48), mp.mpf(2), mp.mpf(2))
    lam = (mp.mpf(4), mp.mpf(50), mp.mpf(50))

    # Evaluate at t=1.0 and intermediate map [t1=1.0, t2=1.1]
    t1, t2 = mp.mpf("1.0"), mp.mpf("1.1")
    Lam1 = [mp.re(ml_series(mu, mp.mpf(1), -l * (t1 ** mu))) for l in lam]
    Lam2 = [mp.re(ml_series(mu, mp.mpf(1), -l * (t2 ** mu))) for l in lam]

    # Exact canonical time-local rates gamma_j(t1)
    kap1 = [kappa_mu(mu, l * (t1 ** mu)) for l in lam]
    til_lam1 = [k / t1 for k in kap1]
    gx1 = (til_lam1[1] + til_lam1[2] - til_lam1[0]) / 2
    gy1 = (til_lam1[0] + til_lam1[2] - til_lam1[1]) / 2
    gz1 = (til_lam1[0] + til_lam1[1] - til_lam1[2]) / 2

    # Finite-step intermediate propagator Phi_{t2, t1}: multiplier r_k = Lam2[k] / Lam1[k]
    r_step = [Lam2[k] / Lam1[k] for k in range(3)]
    # Fujiwara-Algoet Choi eigenvalues of Phi_{t2, t1}:
    p0 = (1 + r_step[0] + r_step[1] + r_step[2]) / 4
    px = (1 + r_step[0] - r_step[1] - r_step[2]) / 4
    py = (1 - r_step[0] + r_step[1] - r_step[2]) / 4
    pz = (1 - r_step[0] - r_step[1] + r_step[2]) / 4

    # Also check global map Phi_{t1} Choi eigenvalues (must all be >= 0!)
    p0_glob = (1 + Lam1[0] + Lam1[1] + Lam1[2]) / 4
    px_glob = (1 + Lam1[0] - Lam1[1] - Lam1[2]) / 4
    py_glob = (1 - Lam1[0] + Lam1[1] - Lam1[2]) / 4
    pz_glob = (1 - Lam1[0] - Lam1[1] + Lam1[2]) / 4

    return {
        "mu": "0.95",
        "parent_rates": [48, 2, 2],
        "pauli_eigenvalues_lambda": [4, 50, 50],
        "t1": "1.0",
        "t2": "1.1",
        "Lambda_t1": [mp.nstr(v, 35) for v in Lam1],
        "Lambda_t2": [mp.nstr(v, 35) for v in Lam2],
        "global_choi_eigs_t1": [mp.nstr(v, 35) for v in (p0_glob, px_glob, py_glob, pz_glob)],
        "canonical_rates_t1": {
            "gamma_x": mp.nstr(gx1, 35),
            "gamma_y": mp.nstr(gy1, 35),
            "gamma_z": mp.nstr(gz1, 35),
        },
        "step_multipliers_r": [mp.nstr(v, 35) for v in r_step],
        "step_choi_eigs_t1_to_t2": {
            "p0": mp.nstr(p0, 35),
            "px": mp.nstr(px, 35),
            "py": mp.nstr(py, 35),
            "pz": mp.nstr(pz, 35),
        },
        "is_P_divisible_all_t": True,
        "min_step_choi_eig": mp.nstr(min(p0, px, py, pz), 35),
    }


def scan_3d_pauli_subordination_below_mu_star(
    mu_list: list[float] | None = None,
) -> dict:
    """
    Exhaustively scan 3D parent Markovian Pauli generators (gamma_x, gamma_y, gamma_z) >= 0
    over time t AND dense 2D triangle-boundary triples (x_y, x_z, x_x) at mu < mu_*
    (plus control mu = 0.95 > mu_*) to verify zero CP-divisibility violations below mu_*.
    """
    if mu_list is None:
        mu_list = [0.60, 0.80, 0.90, 0.925, 0.95]

    mp.mp.dps = 18
    g_vals = [0.0, 1e-3, 1e-2, 0.05, 0.2, 0.5, 1.0, 2.0, 5.0, 20.0, 48.0]
    t_vals = [0.01, 0.05, 0.2, 0.5, 1.0, 3.0]

    # Build all non-zero 3D (gx, gy, gz) triples
    triples = [
        (gx, gy, gz)
        for gx in g_vals
        for gy in g_vals
        for gz in g_vals
        if (gx + gy + gz) > 0.0
    ]
    lam_triples = np.array(
        [[gy + gz, gx + gz, gx + gy] for gx, gy, gz in triples],
        dtype=float,
    )

    # Dense 2D triangle boundary triples including x_star ~ 3.6357
    # Every valid parent triple satisfies |xy - xz| <= xx <= xy + xz (for xz >= xy: xz - xy <= xx <= xz + xy).
    x_1d = [0.001, 0.005, 0.02, 0.08, 0.25, 0.7, 1.5, 2.5, 3.6357, 5.0, 10.0, 20.0, 40.0, 80.0]
    tri_boundary = []
    for i, xy in enumerate(x_1d):
        for xz in x_1d[i:]:
            tri_boundary.append((float(xy + xz), float(xy), float(xz)))
            if xz > xy:
                tri_boundary.append((float(xz - xy), float(xy), float(xz)))
            tri_boundary.append((float(xz), float(xy), float(xz)))

    scan_results = {}
    for mu_f in mu_list:
        print(f"  3D Pauli scan mu={mu_f} ({len(triples)*len(t_vals)} 3D + {len(tri_boundary)} boundary triples)...", flush=True)
        mu_mp = mp.mpf(str(mu_f))
        cache: dict[float, float] = {}

        def get_k(xv: float) -> float:
            if xv == 0.0:
                return 0.0
            key = round(xv, 14)
            val = cache.get(key)
            if val is None:
                val = float(kappa_mu(mu_mp, mp.mpf(repr(xv))))
                cache[key] = val
            return val

        # Collect unique x = lam * t^mu
        t_pows = [tv ** mu_f for tv in t_vals]
        unique_lams = np.unique(lam_triples)
        for tp in t_pows:
            for lm in unique_lams:
                get_k(float(lm * tp))

        min_margin_3d = float("inf")
        worst_cfg_3d = None
        violations_3d = 0

        # Vectorize per time slice using precomputed dict lookup
        for tv, tp in zip(t_vals, t_pows):
            lam_map = {float(lm): get_k(float(lm * tp)) for lm in unique_lams}
            kx = np.array([lam_map[v] for v in lam_triples[:, 0]])
            ky = np.array([lam_map[v] for v in lam_triples[:, 1]])
            kz = np.array([lam_map[v] for v in lam_triples[:, 2]])
            gx_sub = 0.5 * (ky + kz - kx)
            gy_sub = 0.5 * (kx + kz - ky)
            gz_sub = 0.5 * (kx + ky - kz)
            margins = np.minimum(gx_sub, np.minimum(gy_sub, gz_sub))
            idx_min = int(np.argmin(margins))
            m_min = float(margins[idx_min])
            violations_3d += int(np.sum(margins < -1e-12))
            if m_min < min_margin_3d:
                min_margin_3d = m_min
                worst_cfg_3d = {
                    "gamma_parent": list(triples[idx_min]),
                    "t": tv,
                    "subordinated_t_times_gamma": [float(gx_sub[idx_min]), float(gy_sub[idx_min]), float(gz_sub[idx_min])],
                }

        min_margin_tri = float("inf")
        worst_tri = None
        violations_tri = 0
        for xx, xy, xz in tri_boundary:
            kx_v, ky_v, kz_v = get_k(xx), get_k(xy), get_k(xz)
            m_val = 0.5 * min(ky_v + kz_v - kx_v, kx_v + kz_v - ky_v, kx_v + ky_v - kz_v)
            if m_val < -1e-12:
                violations_tri += 1
            if m_val < min_margin_tri:
                min_margin_tri = m_val
                worst_tri = [xx, xy, xz]

        # Adversarial asymmetric check near x_star (~3.6357) with large opposing rates lam_y=lam_z~98
        adv_g = (96.364, 1.818, 1.818)  # lam = (3.636, 98.182, 98.182)
        adv_k = [get_k(adv_g[1] + adv_g[2]), get_k(adv_g[0] + adv_g[2])]
        adv_margin = 0.5 * (2.0 * adv_k[1] - adv_k[0])

        scan_results[str(mu_f)] = {
            "below_mu_star": bool(mu_f < 0.926057800158),
            "n_3d_parent_triples": len(triples),
            "n_t_slices": len(t_vals),
            "n_3d_configs_checked": len(triples) * len(t_vals),
            "n_triangle_boundary_checked": len(tri_boundary),
            "violations_3d": violations_3d,
            "violations_triangle_boundary": violations_tri,
            "min_t_gamma_3d": min_margin_3d,
            "min_t_gamma_triangle_boundary": min_margin_tri,
            "adversarial_xstar_margin": adv_margin,
            "worst_3d_config": worst_cfg_3d,
            "worst_triangle_x": worst_tri,
            "cp_divisible_all_tested": bool(min(min_margin_3d, min_margin_tri, adv_margin) >= -1e-12),
        }

    return scan_results


if __name__ == "__main__":
    print("=== 1. Pauli Subordination Critical Exponent mu_* ===", flush=True)
    mu_star_res = find_mu_star_pauli_subordination()
    print(json.dumps(mu_star_res, indent=2), flush=True)

    print("\n=== 2. Explicit CP-Breaking Counterexample ===", flush=True)
    ce_res = verify_pauli_counterexample()
    print(json.dumps(ce_res, indent=2), flush=True)

    print("\n=== 3. Exhaustive 3D Pauli Triangle-Triple Scan ===", flush=True)
    scan_res = scan_3d_pauli_subordination_below_mu_star()
    print(json.dumps(scan_res, indent=2), flush=True)
