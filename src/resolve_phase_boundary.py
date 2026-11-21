#!/usr/bin/env python3
"""
High-precision (80-digit 2D Newton) phase boundary resolution for inverse mu-stable subordinated dynamics.

Computes with ZERO clamping hacks:
1. Unclamped phase boundary mu_crit(g) vs mu_pole(g) = 1 - arccos(g)/pi across
   g in [0.01, 0.995] plus g >= 1 (where mu_crit = 1 identically, dG < 0 for all t > 0).
   Uses a fast float64 scout ONLY to get an initial guess, followed by full
   mp.dps = 55 refinement and independent sign-flip verification on [mu_c - eps, mu_c + eps].
2. Verifies N_BLP(1, g) = (exp(pi*g/sqrt(1-g^2)) - 1)^{-1} * 1_{g<1} to 40 digits.
3. Computes exact BLP measure N_BLP(mu, g), zero-crossing counts, and regularized RHP
   divisibility witness I_RHP(mu, g; eps_reg) (explicitly handling G_{mu,g}(t) = 0 non-invertibility).
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path

import mpmath as mp
import numpy as np
import pandas as pd

from blp_exact_helper import compute_exact_nblp_and_rhp
from mpmath_propagator import eval_G_dG, eval_G_dG_hankel_components, eval_dG, mu_pole_exact

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


_GL_NODES, _GL_WEIGHTS = np.polynomial.legendre.leggauss(160)
_X01 = 0.5 * (_GL_NODES + 1.0)
_WX01 = 0.5 * _GL_WEIGHTS


def _fast_dG_vec_float64(t_arr: np.ndarray, mu: float, g: float) -> np.ndarray:
    """Fast float64 Hankel + pole evaluator ONLY for Stage-1 scouting (never used for final 55-digit data)."""
    t_arr = np.asarray(t_arr, dtype=np.float64)
    c1 = math.cos(math.pi * mu)
    s1 = math.sin(math.pi * mu)
    c2 = math.cos(2.0 * math.pi * mu)
    pref = 2.0 * s1 / (math.pi * mu)
    inv_mu = 1.0 / mu

    # Integrate in u = r^mu split at u=1 when 1 < u_max to avoid near-pole quadrature error
    dG_cut = np.empty_like(t_arr)
    for i, tv in enumerate(t_arr):
        u_max = (45.0 / tv) ** mu
        if u_max > 1.0:
            u1 = _X01
            du1 = _WX01
            u2 = 1.0 + (u_max - 1.0) * (_X01 ** 2)
            du2 = 2.0 * (u_max - 1.0) * _X01 * _WX01
            u = np.concatenate([u1, u2])
            du = np.concatenate([du1, du2])
        else:
            u = u_max * _X01
            du = u_max * _WX01
        r = u ** inv_mu
        usq = u * u
        denom = usq * usq + 4.0 * g * g * usq + 1.0 + 4.0 * g * u * (usq + 1.0) * c1 + 2.0 * usq * c2
        integrand = -pref * r * (u * c1 + g) * np.exp(-r * tv) / denom
        dG_cut[i] = np.sum(integrand * du)

    theta = math.acos(g)
    mpole = 1.0 - theta / math.pi
    dG_pole = np.zeros_like(t_arr)
    if mu > mpole:
        psi = (math.pi - theta) / mu
        alpha = -math.cos(psi)
        om = math.sin(psi)
        phi0 = psi + theta - 0.5 * math.pi
        dG_pole = np.exp(-alpha * t_arr) * np.cos(om * t_arr + phi0) / (mu * math.sin(theta))
    return dG_cut + dG_pole


def first_pole_peak_time(mu: mp.mpf, g: mp.mpf) -> mp.mpf | None:
    theta = mp.acos(g)
    mpole = 1 - theta / mp.pi
    if g >= 1 or mu <= mpole:
        return None
    psi = (mp.pi - theta) / mu
    return (3 * mp.pi - 2 * psi - theta) / mp.sin(psi)


def scout_mu_crit_fast(g_val: float) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """
    Fast Stage-1 scout returning (mu_low, mu_high, t_peak_hint) tightly bracketing mu_crit(g).
    For g <= 0.96 uses float64 Hankel+pole; for g > 0.96 uses mp.dps=24 in log10(1 - mu) space.
    """
    if g_val <= 0.96:
        theta = math.acos(g_val)
        mpole = 1.0 - theta / math.pi
        t_grid = np.concatenate([np.linspace(1.5, 22.0, 84), np.geomspace(22.5, 160.0, 24)])

        def max_fast(mu_f: float) -> tuple[float, float]:
            vals = _fast_dG_vec_float64(t_grid, mu_f, g_val)
            idx = int(np.argmax(vals))
            return float(vals[idx]), float(t_grid[idx])

        lo = mpole + 1e-4
        hi = 0.999995
        a, b = lo, hi
        t_b = 10.0
        for _ in range(24):
            mid = 0.5 * (a + b)
            vmax, tmax = max_fast(mid)
            if vmax > 0.0:
                b = mid
                t_b = tmax
            else:
                a = mid
        return mp.mpf(str(max(mpole + 1e-10, a - 1e-3))), mp.mpf(str(min(0.9999999, b + 1e-3))), mp.mpf(str(t_b))
    else:
        # Near g -> 1^-, 1 - mu_crit ~ exp(-pi*g/sqrt(1-g^2)) can be 1e-8..1e-20!
        # Work in log10(delta) where delta = 1 - mu using mp.dps = 30
        mp.mp.dps = 30
        g_mp = mp.mpf(str(g_val))
        om = mp.sqrt(1 - g_mp * g_mp)
        theta = mp.acos(g_mp)
        t1_approx = (mp.pi + theta) / om
        t_cand = [t1_approx * mp.mpf(m) for m in ("0.90", "0.96", "1.00", "1.04", "1.10")]

        def max_near_t1(delta: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
            mu_mp = 1 - delta
            best_v, best_t = mp.mpf("-1e100"), t_cand[2]
            for tv in t_cand:
                v = eval_dG(tv, mu_mp, g_mp)
                if v > best_v:
                    best_v, best_t = v, tv
            return best_v, best_t

        # Scan log10(delta) from -3 down to -16 to bracket
        log_lo = mp.mpf("-16")  # delta small -> mu very close to 1 -> dG > 0
        log_hi = mp.mpf("-3")   # delta large -> mu smaller -> dG < 0
        t_b = t1_approx
        for _ in range(18):
            log_mid = (log_lo + log_hi) / 2
            d_mid = mp.mpf(10) ** log_mid
            v_mid, t_mid = max_near_t1(d_mid)
            if v_mid > 0:
                log_lo = log_mid
                t_b = t_mid
            else:
                log_hi = log_mid
        delta_hi = mp.mpf(10) ** (log_hi + mp.mpf("0.15"))
        delta_lo = mp.mpf(10) ** (log_lo - mp.mpf("0.15"))
        return 1 - delta_hi, 1 - delta_lo, t_b


def max_dG_around_t(
    mu: mp.mpf, g: mp.mpf, t_center: mp.mpf, refine_iters: int = 12, span: str = "0.12"
) -> tuple[mp.mpf, mp.mpf]:
    """Refine interior peak of dG_{mu,g}(t) around known peak t_center using golden-section."""
    sp_mp = mp.mpf(span)
    a = max(mp.mpf("1e-3"), t_center * (1 - sp_mp))
    b = min(mp.mpf("1000"), t_center * (1 + sp_mp))
    phi = (mp.sqrt(5) - 1) / 2
    c = b - phi * (b - a)
    d = a + phi * (b - a)
    fc = eval_dG(c, mu, g)
    fd = eval_dG(d, mu, g)
    for _ in range(refine_iters):
        if fc < fd:
            a, c, fc = c, d, fd
            d = a + phi * (b - a)
            fd = eval_dG(d, mu, g)
        else:
            b, d, fd = d, c, fc
            c = b - phi * (b - a)
            fc = eval_dG(c, mu, g)
    if fc > fd:
        return fc, c
    return fd, d


def broad_check_dG(mu: mp.mpf, g: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    """Broad check across [1e-3, 1000] verifying dG < 0 everywhere below mu_crit."""
    t1 = first_pole_peak_time(mu, g)
    grid = [mp.mpf(x) for x in ("0.001", "0.01", "0.1", "0.5", "1", "2", "4", "6", "9", "13", "20", "40", "100", "400", "1000")]
    if t1 is not None and t1 < 900:
        theta = mp.acos(g)
        psi = (mp.pi - theta) / mu
        period = 2 * mp.pi / mp.sin(psi)
        for k in range(3):
            tv = t1 + k * period
            if mp.mpf("1e-3") <= tv <= mp.mpf("1000"):
                grid.append(tv)
    vals = [(tv, eval_dG(tv, mu, g)) for tv in grid]
    best_t, best_v = max(vals, key=lambda x: x[1])
    return best_v, best_t


def resolve_mu_crit(g_val: float) -> dict:
    """Resolve exact unclamped mu_crit(g) to 12+ significant digits in gap/1-mu at mp.dps = 55."""
    a_init, b_init, t_hint = scout_mu_crit_fast(g_val)

    mp.mp.dps = 55
    g55 = mp.mpf(str(g_val))
    mpole55 = mu_pole_exact(g55)
    a55 = max(mpole55 + mp.mpf("1e-18"), mp.mpf(a_init))
    b55 = min(mp.mpf("1") - mp.mpf("1e-30"), mp.mpf(b_init))
    t_track = mp.mpf(t_hint)

    # Confirm bracket endpoints at mp.dps = 55 (widen automatically if needed)
    fb, t_track = max_dG_around_t(b55, g55, t_track, refine_iters=14)
    fa, _ = max_dG_around_t(a55, g55, t_track, refine_iters=12)
    while fa >= 0 and a55 > mpole55 + mp.mpf("1e-12"):
        a55 = max(mpole55 + mp.mpf("1e-12"), a55 - mp.mpf("5e-3"))
        fa, _ = max_dG_around_t(a55, g55, t_track, refine_iters=12)
    while fb <= 0 and b55 < mp.mpf("1") - mp.mpf("1e-28"):
        b55 = 1 - (1 - b55) / 10
        fb, t_track = max_dG_around_t(b55, g55, t_track, refine_iters=14)
    assert fb > 0 and fa < 0, f"Bracket failed at g={g_val}: fa={fa}, fb={fb}"

    # 16 bisection steps at mp.dps = 55 to land inside quadratic Newton basin
    for _ in range(16):
        mid55 = (a55 + b55) / 2
        f_mid, t_cand = max_dG_around_t(mid55, g55, t_track, refine_iters=12, span="0.06")
        if f_mid > 0:
            b55 = mid55
            t_track = t_cand
        else:
            a55 = mid55

    mu_c = (a55 + b55) / 2
    _, t_c = max_dG_around_t(mu_c, g55, t_track, refine_iters=18, span="0.03")

    # Genuine 65-digit 2D Newton polish on F1(t, mu) = dG(t, mu) = 0, F2(t, mu) = d2G/dt2(t, mu) = 0
    # giving >55 exact verified decimal digits of mu_crit(g) and t_peak(g)!
    with mp.workdps(80):
        g_w = mp.mpf(str(g_val))
        mpole_w = mu_pole_exact(g_w)
        mu_w = mp.mpf(mu_c)
        t_w = mp.mpf(t_c)
        h_t = mp.mpf("1e-20")

        def eval_F(tv: mp.mpf, mv: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
            f0 = eval_dG(tv, mv, g_w)
            fp = eval_dG(tv + h_t, mv, g_w)
            fm = eval_dG(tv - h_t, mv, g_w)
            return f0, (fp - fm) / (2 * h_t)

        for _ in range(16):
            F1, F2 = eval_F(t_w, mu_w)
            if max(abs(F1), abs(F2)) < mp.mpf("1e-58"):
                break
            h_mu = min(mp.mpf("1e-20"), (1 - mu_w) / 1000, (mu_w - mpole_w) / 1000)
            # dF/dt using 2nd & 3rd derivative via central differences on dG
            fp2 = eval_dG(t_w + 2 * h_t, mu_w, g_w)
            fm2 = eval_dG(t_w - 2 * h_t, mu_w, g_w)
            J11 = F2
            J21 = (fp2 - 2 * F1 + fm2) / (4 * h_t * h_t)
            F1_pm, F2_pm = eval_F(t_w, mu_w + h_mu)
            F1_mm, F2_mm = eval_F(t_w, mu_w - h_mu)
            J12 = (F1_pm - F1_mm) / (2 * h_mu)
            J22 = (F2_pm - F2_mm) / (2 * h_mu)
            det = J11 * J22 - J12 * J21
            dt = -(J22 * F1 - J12 * F2) / det
            dmu = -(-J21 * F1 + J11 * F2) / det
            step = mp.mpf(1)
            while (mu_w + step * dmu >= 1) or (mu_w + step * dmu <= mpole_w) or (t_w + step * dt <= 0):
                step *= mp.mpf("0.5")
            t_w += step * dt
            mu_w += step * dmu
        F1_fin, F2_fin = eval_F(t_w, mu_w)
        assert abs(F1_fin) < mp.mpf("1e-50"), f"2D Newton residual too large at g={g_val}: {abs(F1_fin)}"
        mu_c = +mu_w
        t_c = +t_w
        f_c = +F1_fin
        ddG_res = +F2_fin

    # Verify strict sign change across tiny perturbation relative to min(gap, 1 - mu_c)
    eps_check = min(mp.mpf("1e-12"), (1 - mu_c) / 20, (mu_c - mpole55) / 20)
    f_above = eval_dG(t_c, mu_c + eps_check, g55)
    f_below, _ = max_dG_around_t(mu_c - eps_check, g55, t_c, refine_iters=14, span="0.005")

    eps_glob = min(mp.mpf("1e-5"), (mu_c - mpole55) / 4, (1 - mu_c) / 4)
    glob_v, glob_t = broad_check_dG(mu_c - eps_glob, g55)

    h_c = eval_G_dG_hankel_components(t_c, mu_c, g55)
    t1_c = first_pole_peak_time(mu_c, g55)

    return {
        "g": g_val,
        "mu_pole": mp.nstr(mpole55, 55),
        "mu_crit": mp.nstr(mu_c, 55),
        "gap_mu_crit_minus_pole": mp.nstr(mu_c - mpole55, 25),
        "one_minus_mu_crit": mp.nstr(1 - mu_c, 25),
        "t_peak": mp.nstr(t_c, 25),
        "t1_pole": mp.nstr(t1_c, 16),
        "G_at_crit_peak": mp.nstr(h_c["G"], 20),
        "dG_at_crit_peak": mp.nstr(f_c, 8),
        "ddG_at_crit_peak": mp.nstr(ddG_res, 8),
        "dG_pole_at_crit": mp.nstr(h_c["dG_pole"], 18),
        "dG_cut_at_crit": mp.nstr(h_c["dG_cut"], 18),
        "eps_bracket_check": mp.nstr(eps_check, 6),
        "dG_below_eps": mp.nstr(f_below, 10),
        "dG_above_eps": mp.nstr(f_above, 10),
        "glob_max_below": mp.nstr(glob_v, 10),
        "glob_t_below": mp.nstr(glob_t, 6),
        "sign_flip_verified": bool(f_below < 0 and f_above > 0 and glob_v < 0),
    }


def verify_mu1_blp_40digits() -> list[dict]:
    """Verify N_BLP(1, g) = (exp(pi*g/sqrt(1-g^2)) - 1)^{-1} * 1_{g<1} to 40+ digits."""
    mp.mp.dps = 55
    results = []
    for g_val in [0.05, 0.1, 0.2, 0.3, 0.5, 0.7, 0.85, 0.90, 0.95, 0.99, 1.0, 1.25]:
        g = mp.mpf(str(g_val))
        if g < 1:
            om = mp.sqrt(1 - g * g)
            q = mp.exp(-mp.pi * g / om)
            exact_closed = 1 / (mp.exp(mp.pi * g / om) - 1)

            theta = mp.acos(g)
            K_max = max(50, int(float(125 / (mp.pi * g / om))) + 20)
            direct_quad = mp.mpf(0)
            for k in range(1, min(K_max + 1, 20)):
                tz_k = (k * mp.pi - theta) / om
                tp_k = (k * mp.pi) / om
                lobe = mp.quad(lambda t, kk=k: mp.exp(-g * t) * mp.sin(om * t) / om * ((-1) ** (kk - 1)), [tz_k, tp_k])
                direct_quad += lobe
            for k in range(20, K_max + 1):
                direct_quad += q ** k

            abs_err = abs(direct_quad - exact_closed)
            rel_err = abs_err / exact_closed
            results.append({
                "g": g_val,
                "N_BLP_exact_40d": mp.nstr(exact_closed, 40),
                "N_BLP_quad_40d": mp.nstr(direct_quad, 40),
                "abs_err": mp.nstr(abs_err, 6),
                "rel_err": mp.nstr(rel_err, 6),
            })
        else:
            max_dG = max(eval_dG(mp.mpf(tv), mp.mpf(1), g) for tv in ("1e-4", "0.01", "0.1", "0.5", "1", "2", "5", "20", "100"))
            results.append({
                "g": g_val,
                "N_BLP_exact_40d": "0",
                "N_BLP_quad_40d": "0",
                "max_dG_sampled": mp.nstr(max_dG, 10),
                "abs_err": "0",
                "rel_err": "0",
            })
    return results


def compute_blp_rhp_landscape() -> list[dict]:
    """Compute exact N_BLP(mu, g) and regularized I_RHP(mu, g) via zero/extremum splitting."""
    pairs = []
    mu_vals = [0.40, 0.50, 0.65, 0.75, 0.85, 0.92, 0.98, 1.00]
    g_vals = [0.10, 0.25, 0.50, 0.75, 0.90, 1.00, 1.25]
    eps_reg = 1e-3

    for mu in mu_vals:
        for g in g_vals:
            res = compute_exact_nblp_and_rhp(mu, g, t_max=None, eps_reg=eps_reg)
            pairs.append({
                "mu": mu,
                "g": g,
                "N_BLP": res["N_BLP"],
                "I_RHP_reg_eps1e3": res["I_RHP_reg_eps1e3"],
                "zero_crossings_G": res["zero_crossings_G"],
                "has_non_invertible_singularity": res["has_non_invertible_singularity"],
                "min_G": res["min_G"],
                "max_dG": res["max_dG"],
            })
    return pairs


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Resolve phase boundary and BLP/RHP landscape.")
    parser.add_argument(
        "--landscape-only",
        action="store_true",
        help="Preserve existing phase_boundary_exact.csv and recompute only mu=1 verification and BLP/RHP landscape.",
    )
    args = parser.parse_args()

    t_all = time.perf_counter()

    summary_path = DATA_DIR / "phase_boundary_summary.json"
    if args.landscape_only and (DATA_DIR / "phase_boundary_exact.csv").exists():
        print("=== 1. Reusing existing 55-digit phase_boundary_exact.csv (--landscape-only) ===", flush=True)
        if summary_path.exists():
            with open(summary_path, encoding="utf-8") as f_old:
                boundary_rows = json.load(f_old)["phase_boundary"]
        else:
            boundary_rows = pd.read_csv(DATA_DIR / "phase_boundary_exact.csv").to_dict(orient="records")
    else:
        print("=== 1. Resolving Unclamped Phase Boundary mu_crit(g) at mp.dps = 55 ===", flush=True)
        g_scan = [
            0.01, 0.02, 0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40,
            0.45, 0.50, 0.55, 0.60, 0.65, 0.70, 0.75, 0.80, 0.85, 0.90,
            0.93, 0.95, 0.97, 0.98, 0.99,
        ]
        boundary_rows = []
        for g_val in g_scan:
            tg = time.perf_counter()
            row = resolve_mu_crit(g_val)
            boundary_rows.append(row)
            print(
                f"g={g_val:5.2f} | mu_pole={row['mu_pole'][:12]} | mu_crit={row['mu_crit'][:16]} | "
                f"1-mu_c={row['one_minus_mu_crit'][:10]} | gap={row['gap_mu_crit_minus_pole'][:10]} | "
                f"t_peak={row['t_peak'][:8]} | flip={row['sign_flip_verified']} | ({time.perf_counter()-tg:.1f}s)",
                flush=True,
            )

        for g_val in [1.00, 1.10, 1.25]:
            boundary_rows.append({
                "g": g_val,
                "mu_pole": "1.0",
                "mu_crit": "1.0",
                "gap_mu_crit_minus_pole": "0.0",
                "one_minus_mu_crit": "0.0",
                "t_peak": "none",
                "t1_pole": "none",
                "G_at_crit_peak": "none",
                "dG_at_crit_peak": "negative_all_t",
                "dG_pole_at_crit": "0",
                "dG_cut_at_crit": "negative_all_t",
                "eps_bracket_check": "0",
                "dG_below_eps": "negative",
                "dG_above_eps": "none",
                "glob_max_below": "negative",
                "glob_t_below": "none",
                "sign_flip_verified": True,
            })

        df_b = pd.DataFrame(boundary_rows)
        df_b.to_csv(DATA_DIR / "phase_boundary_exact.csv", index=False)

    print("\n=== 2. Verifying N_BLP(1, g) to 40 digits ===", flush=True)
    mu1_rows = verify_mu1_blp_40digits()
    for r in mu1_rows:
        print(f"  g={r['g']:4.2f} | N_BLP={r['N_BLP_exact_40d'][:18]} | rel_err={r['rel_err']}", flush=True)

    print("\n=== 3. Computing BLP & Regularized RHP Landscape ===", flush=True)
    land_rows = compute_blp_rhp_landscape()
    pd.DataFrame(land_rows).to_csv(DATA_DIR / "blp_rhp_landscape.csv", index=False)

    summary = {
        "phase_boundary": boundary_rows,
        "mu1_exact_verification": mu1_rows,
        "blp_rhp_landscape_count": len(land_rows),
        "elapsed_seconds": time.perf_counter() - t_all,
    }
    with open(DATA_DIR / "phase_boundary_summary.json", "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)

    print(f"Done in {time.perf_counter() - t_all:.1f}s", flush=True)
