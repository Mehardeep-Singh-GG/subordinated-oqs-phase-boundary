#!/usr/bin/env python3
"""
Exact zero/extremum summation helper for N_BLP(mu, g) and regularized I_RHP(mu, g; eps_reg).

Uses Proposition 1(b): between consecutive zeros of G_{mu,g}(t), extrema (roots of dG_{mu,g}(t)=0),
and threshold crossings |G_{mu,g}(t)| = eps_reg, |G(t)| is strictly monotone and sigma_BLP(t) has
constant sign, so both N_BLP and I_RHP_reg evaluate analytically without quadrature error across
|G(t)| = 0 cusps:
  - N_BLP interval contribution (when sigma > 0): |G(b)| - |G(a)|
  - I_RHP_reg interval contribution (when sigma > 0):
      (|G(b)| - |G(a)|) / eps_reg   if |G| <= eps_reg on (a, b)
      ln(|G(b)| / |G(a)|)           if |G| >= eps_reg on (a, b)
      (eps_reg - |G(a)|)/eps_reg + ln(|G(b)|/eps_reg) if |G(a)| < eps_reg < |G(b)|
For mu = 1, g < 1, evaluates the full [0, inf) closed-form geometric sums directly.
For g >= 1 or mu <= mu_pole(g), Theorem 4 proves N_BLP = I_RHP_reg = 0 identically.
"""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np
from scipy.optimize import brentq

from mpmath_propagator import eval_G_dG

_GL_NODES, _GL_WEIGHTS = np.polynomial.legendre.leggauss(192)
_X01 = 0.5 * (_GL_NODES + 1.0)
_WX01 = 0.5 * _GL_WEIGHTS


def _make_fast_float64_eval(mu: float, g: float):
    """Build a fast closure for float64 Hankel+pole G(t), dG(t) evaluation (~1e-13..1e-15 accuracy)."""
    c1 = math.cos(math.pi * mu)
    s1 = math.sin(math.pi * mu)
    c2 = math.cos(2.0 * math.pi * mu)
    pref = 2.0 * s1 / (math.pi * mu)
    inv_mu = 1.0 / mu
    theta = math.acos(min(1.0, max(-1.0, g))) if g <= 1.0 else 0.0
    mpole = (1.0 - theta / math.pi) if g < 1.0 else 1.0
    has_pole = (g < 1.0 and mu > mpole)
    if has_pole:
        psi = (math.pi - theta) / mu
        alpha = -math.cos(psi)
        om = math.sin(psi)
        denom_p = mu * math.sin(theta)
        sa = math.cos((math.pi * mu - theta) * 0.5)
        sb = math.sin((math.pi * (mu - mpole)) * 0.5)
    else:
        psi = alpha = om = denom_p = sa = sb = 0.0
        if g < 1.0:
            sa = math.cos((math.pi * mu - theta) * 0.5)
            sb = math.sin((math.pi * (mu - mpole)) * 0.5)

    def eval_scalar(tv: float) -> tuple[float, float]:
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
        if g < 1.0:
            um1 = u - 1.0
            denom = (um1 * um1 + 4.0 * u * sa * sa) * (um1 * um1 + 4.0 * u * sb * sb)
        else:
            usq = u * u
            denom = usq * usq + 4.0 * g * g * usq + 1.0 + 4.0 * g * u * (usq + 1.0) * c1 + 2.0 * usq * c2
        common = pref * (u * c1 + g) * np.exp(-r * tv) / denom * du
        G_c = float(np.sum(common))
        dG_c = float(-np.sum(r * common))
        if has_pole:
            ep = math.exp(-alpha * tv) / denom_p
            G_c += ep * math.sin(om * tv + theta)
            dG_c += ep * math.sin(om * tv + theta + psi)
        return G_c, dG_c

    def eval_vec(t_arr: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        t_arr = np.asarray(t_arr, dtype=np.float64)
        Gs = np.empty_like(t_arr)
        dGs = np.empty_like(t_arr)
        for i, tv in enumerate(t_arr):
            Gs[i], dGs[i] = eval_scalar(float(tv))
        return Gs, dGs

    return eval_scalar, eval_vec


def _fast_G_dG_vec_float64(t_arr: np.ndarray, mu: float, g: float) -> tuple[np.ndarray, np.ndarray]:
    _, vec_fn = _make_fast_float64_eval(mu, g)
    return vec_fn(t_arr)


def _refine_root_mp(
    fn,
    a: mp.mpf,
    b: mp.mpf,
    fa: mp.mpf,
    fb: mp.mpf,
    tol: mp.mpf = mp.mpf("1e-14"),
    max_iters: int = 40,
) -> mp.mpf:
    """Safely refine simple root on [a, b] with f(a)*f(b) <= 0 using secant-bisection."""
    if fa == 0:
        return a
    if fb == 0:
        return b
    lo, hi = (a, b) if a < b else (b, a)
    flo, fhi = (fa, fb) if a < b else (fb, fa)
    for it in range(max_iters):
        width = hi - lo
        if width <= tol * max(mp.mpf(1), lo):
            break
        if it % 3 != 2 and fhi != flo:
            s = lo - flo * width / (fhi - flo)
            if lo + mp.mpf("0.05") * width < s < hi - mp.mpf("0.05") * width:
                mid = s
            else:
                mid = (lo + hi) / 2
        else:
            mid = (lo + hi) / 2
        fmid = fn(mid)
        if fmid == 0:
            return mid
        if (flo > 0 and fmid < 0) or (flo < 0 and fmid > 0):
            hi, fhi = mid, fmid
        else:
            lo, flo = mid, fmid
    return (lo + hi) / 2


def compute_exact_mu1(g_val: float, eps_reg: float = 1e-3, t_window_max: float | None = None) -> dict:
    """Closed-form exact [0, inf) (or [0, t_window_max] if given) N_BLP and I_RHP_reg for mu = 1."""
    if g_val >= 1.0:
        mp.mp.dps = 28
        g_mp = mp.mpf(str(g_val))
        t_ref = mp.mpf("60") if t_window_max is None else mp.mpf(str(t_window_max))
        min_G_v, _ = eval_G_dG(t_ref, mp.mpf(1), g_mp)
        max_dG_v = mp.mpf("-1e-5") if g_val == 1.0 else eval_G_dG(mp.mpf("1e-4"), mp.mpf(1), g_mp)[1]
        return {
            "mu": 1.0,
            "g": g_val,
            "N_BLP": 0.0,
            "I_RHP_reg_eps1e3": 0.0,
            "zero_crossings_G": 0,
            "dG_positive_lobes": 0,
            "sigma_BLP_positive_lobes": 0,
            "last_positive_sigma_t": 0.0,
            "has_non_invertible_singularity": False,
            "min_G": float(min_G_v),
            "max_dG": float(max_dG_v),
        }

    mp.mp.dps = 35
    g = mp.mpf(str(g_val))
    eps = mp.mpf(str(eps_reg))
    om = mp.sqrt(1 - g * g)
    theta = mp.acos(g)
    q = mp.exp(-mp.pi * g / om)
    if t_window_max is None:
        n_blp = 1 / (mp.exp(mp.pi * g / om) - 1)
        ln_q = -mp.pi * g / om
        k_cut = int(mp.floor(mp.log(eps) / ln_q)) if q > eps else 0
        ln_eps = mp.log(eps)
        part_above = k_cut * (1 - ln_eps) + ln_q * k_cut * (k_cut + 1) / 2
        part_below = (q ** (k_cut + 1)) / (eps * (1 - q))
        i_rhp = part_above + part_below
        min_G_v = -q
        max_dG_v = mp.exp(-g * (mp.pi + theta) / om)
        return {
            "mu": 1.0,
            "g": g_val,
            "N_BLP": float(n_blp),
            "I_RHP_reg_eps1e3": float(i_rhp),
            "zero_crossings_G": -1,
            "dG_positive_lobes": -1,
            "sigma_BLP_positive_lobes": -1,
            "last_positive_sigma_t": float("inf"),
            "has_non_invertible_singularity": True,
            "min_G": float(min_G_v),
            "max_dG": float(max_dG_v),
        }

    tw = mp.mpf(str(t_window_max))
    n_blp = mp.mpf(0)
    i_rhp = mp.mpf(0)
    zeros = 0
    k = 1
    last_t = mp.mpf(0)
    sig_lobes = 0
    dG_lobes = 0
    while True:
        zk = (k * mp.pi - theta) / om
        ek = (k * mp.pi) / om
        if zk >= tw:
            break
        zeros += 1
        sig_lobes += 1
        if ek >= tw:
            Gk_w, _ = eval_G_dG(tw, mp.mpf(1), g)
            d_end = abs(Gk_w)
            n_blp += d_end
            i_rhp += (d_end / eps) if d_end <= eps else (1 + mp.log(d_end / eps))
            last_t = tw
            break
        d_ext = q ** k
        n_blp += d_ext
        i_rhp += (d_ext / eps) if d_ext <= eps else (1 + mp.log(d_ext / eps))
        last_t = ek
        if k % 2 == 1:
            dG_lobes += 1
        k += 1
    return {
        "mu": 1.0,
        "g": g_val,
        "N_BLP": float(n_blp),
        "I_RHP_reg_eps1e3": float(i_rhp),
        "zero_crossings_G": zeros,
        "dG_positive_lobes": dG_lobes,
        "sigma_BLP_positive_lobes": sig_lobes,
        "last_positive_sigma_t": float(last_t),
        "has_non_invertible_singularity": bool(zeros > 0),
        "min_G": float(-q) if (mp.pi / om) <= tw else float(eval_G_dG(tw, mp.mpf(1), g)[0]),
        "max_dG": float(mp.exp(-g * (mp.pi + theta) / om)) if ((mp.pi + theta) / om) <= tw else 0.0,
    }


def compute_exact_nblp_and_rhp(
    mu_val: float,
    g_val: float,
    t_max: float | None = None,
    eps_reg: float = 1e-3,
    dps: int = 22,
) -> dict:
    """
    Compute exact N_BLP(mu, g) and I_RHP_reg(mu, g; eps_reg) via Proposition 1(b)
    root/extremum decomposition.
    """
    if abs(mu_val - 1.0) < 1e-12:
        return compute_exact_mu1(g_val, eps_reg=eps_reg, t_window_max=t_max)

    mp.mp.dps = dps
    mu_mp = mp.mpf(str(mu_val))
    g_mp = mp.mpf(str(g_val))
    eps_mp = mp.mpf(str(eps_reg))

    mpole_f = (1.0 - math.acos(g_val) / math.pi) if g_val < 1.0 else 1.0
    if g_val >= 1.0 or mu_val <= mpole_f + 1e-14:
        t_eval = 60.0 if t_max is None else t_max
        G_end, dG_end = eval_G_dG(mp.mpf(str(t_eval)), mu_mp, g_mp)
        _, dG_start = eval_G_dG(mp.mpf("1e-4"), mu_mp, g_mp)
        return {
            "mu": mu_val,
            "g": g_val,
            "N_BLP": 0.0,
            "I_RHP_reg_eps1e3": 0.0,
            "zero_crossings_G": 0,
            "dG_positive_lobes": 0,
            "sigma_BLP_positive_lobes": 0,
            "last_positive_sigma_t": 0.0,
            "leading_asymptotic_envelope_crossover_t": None,
            "has_non_invertible_singularity": False,
            "min_G": float(G_end),
            "max_dG": float(max(dG_start, dG_end)),
        }

    theta = math.acos(g_val)
    psi = (math.pi - theta) / mu_val
    alpha = -math.cos(psi)
    om = math.sin(psi)
    period = 2.0 * math.pi / max(1e-6, om)
    C_cut = 2.0 * g_val * math.sin(math.pi * mu_val) * math.gamma(mu_val + 1.0) / math.pi
    A_pole = 1.0 / (mu_val * math.sin(theta))

    t_asymp = None
    if C_cut > 0 and alpha > 0:
        t_cur = max(5.0, 2.0 / alpha)
        rhs = math.log(A_pole / C_cut)
        for _ in range(40):
            f_t = alpha * t_cur - (mu_val + 1.0) * math.log(t_cur) - rhs
            df_t = alpha - (mu_val + 1.0) / t_cur
            t_next = max(1.0, t_cur - f_t / max(1e-9, df_t))
            if abs(t_next - t_cur) < 1e-12:
                t_cur = t_next
                break
            t_cur = t_next
        t_asymp = t_cur

    if t_max is None:
        t_tail_est = (t_asymp * 1.15 + period + 6.0) if t_asymp is not None else 60.0
        t_end = min(220.0, max(60.0, t_tail_est))
    else:
        t_end = float(t_max)

    t_osc_end = min(t_end, max(30.0, (20.0 / max(alpha, 1e-4)) if alpha > 0 else t_end))
    dt = min(0.08, period / 24.0)
    n_dense = min(4000, max(120, int(math.ceil(t_osc_end / dt)) + 1))
    t_dense = np.linspace(1e-4, t_osc_end, n_dense)
    if t_end > t_osc_end + 0.1:
        t_sparse = np.linspace(t_osc_end, t_end, max(40, int((t_end - t_osc_end) / max(0.25, period / 16.0))))
        t_scan = np.concatenate([t_dense, t_sparse[1:]])
    else:
        t_scan = t_dense

    eval_f64_scalar, eval_f64_vec = _make_fast_float64_eval(mu_val, g_val)
    G_f64, dG_f64 = eval_f64_vec(t_scan)

    zero_brackets = []
    ext_brackets = []
    for i in range(len(t_scan) - 1):
        if G_f64[i] == 0.0 or (G_f64[i] * G_f64[i + 1] <= 0.0):
            zero_brackets.append((float(t_scan[i]), float(t_scan[i + 1])))
        if dG_f64[i] == 0.0 or (dG_f64[i] * dG_f64[i + 1] <= 0.0):
            ext_brackets.append((float(t_scan[i]), float(t_scan[i + 1])))
        if 0 < i < len(t_scan) - 1:
            if dG_f64[i] > dG_f64[i - 1] and dG_f64[i] >= dG_f64[i + 1] and -1e-4 < dG_f64[i] <= 0:
                for frac in (0.35, 0.5, 0.65):
                    tm = float(t_scan[i - 1] + frac * (t_scan[i + 1] - t_scan[i - 1]))
                    dGm = float(eval_G_dG(mp.mpf(str(tm)), mu_mp, g_mp)[1])
                    if dGm > 0:
                        ext_brackets.append((float(t_scan[i - 1]), tm))
                        ext_brackets.append((tm, float(t_scan[i + 1])))
                        break

    def fn_G_mp(tv: mp.mpf) -> mp.mpf:
        return eval_G_dG(tv, mu_mp, g_mp)[0]

    def fn_dG_mp(tv: mp.mpf) -> mp.mpf:
        return eval_G_dG(tv, mu_mp, g_mp)[1]

    # When float64 is well within precision (g <= 0.94 and away from cut), float64 brentq
    # finds every root to ~1e-13; polish with mpmath for large roots (|G| >= 1e-8) or tight g.
    need_mp_roots = (g_val > 0.94) or ((mu_val - mpole_f) < 0.015)

    zeros_mp: list[mp.mpf] = []
    for ta_f, tb_f in zero_brackets:
        r0 = brentq(lambda tv: eval_f64_scalar(tv)[0], ta_f, tb_f, xtol=1e-13, rtol=1e-13, maxiter=50)
        if need_mp_roots:
            ta_n = mp.mpf(str(max(ta_f, r0 - 1e-8)))
            tb_n = mp.mpf(str(min(tb_f, r0 + 1e-8)))
            fa, fb = fn_G_mp(ta_n), fn_G_mp(tb_n)
            rt = _refine_root_mp(fn_G_mp, ta_n, tb_n, fa, fb) if fa * fb <= 0 else mp.mpf(str(r0))
        else:
            rt = mp.mpf(str(r0))
        if not zeros_mp or abs(rt - zeros_mp[-1]) > mp.mpf("1e-10"):
            zeros_mp.append(rt)

    exts_mp: list[mp.mpf] = []
    for idx_e, (ta_f, tb_f) in enumerate(ext_brackets):
        r0 = brentq(lambda tv: eval_f64_scalar(tv)[1], ta_f, tb_f, xtol=1e-13, rtol=1e-13, maxiter=50)
        g_at_r0, _ = eval_f64_scalar(r0)
        if need_mp_roots or (idx_e < 4 and abs(g_at_r0) > 1e-6):
            ta_n = mp.mpf(str(max(ta_f, r0 - 1e-9)))
            tb_n = mp.mpf(str(min(tb_f, r0 + 1e-9)))
            fa, fb = fn_dG_mp(ta_n), fn_dG_mp(tb_n)
            if fa * fb <= 0:
                rt = _refine_root_mp(fn_dG_mp, ta_n, tb_n, fa, fb, tol=mp.mpf("1e-13"))
            else:
                rt = mp.mpf(str(r0))
        else:
            rt = mp.mpf(str(r0))
        if not exts_mp or abs(rt - exts_mp[-1]) > mp.mpf("1e-10"):
            exts_mp.append(rt)

    t_end_mp = mp.mpf(str(t_end))
    crit_points: list[tuple[mp.mpf, str, mp.mpf]] = [(mp.mpf(0), "start", mp.mpf(1))]
    for z in zeros_mp:
        crit_points.append((z, "zero", mp.mpf(0)))
    for idx_e, e in enumerate(exts_mp):
        ge_f64, _ = eval_f64_scalar(float(e))
        Ge = fn_G_mp(e) if (need_mp_roots or (idx_e < 6 and abs(ge_f64) > 1e-9)) else mp.mpf(str(ge_f64))
        crit_points.append((e, "ext", Ge))
    G_end, dG_end = eval_G_dG(t_end_mp, mu_mp, g_mp)
    crit_points.append((t_end_mp, "end", G_end))
    crit_points.sort(key=lambda item: item[0])

    merged: list[tuple[mp.mpf, str, mp.mpf]] = []
    for item in crit_points:
        if not merged or abs(item[0] - merged[-1][0]) > mp.mpf("1e-10"):
            merged.append(item)

    n_blp = mp.mpf(0)
    i_rhp = mp.mpf(0)
    sig_lobes = 0
    in_sig_lobe = False
    last_pos_sigma_t = mp.mpf(0)

    for idx in range(len(merged) - 1):
        ta, _, Ga = merged[idx]
        tb, _, Gb = merged[idx + 1]
        if tb <= ta + mp.mpf("1e-11"):
            continue
        tm_f = float((ta + tb) / 2)
        Gm_f, dGm_f = eval_f64_scalar(tm_f)
        sig_f = dGm_f if Gm_f >= 0.0 else -dGm_f
        if need_mp_roots or abs(sig_f) < 1e-8 or abs(Gm_f) < 1e-8:
            Gm_m, dGm_m = eval_G_dG((ta + tb) / 2, mu_mp, g_mp)
            is_pos = (dGm_m > 0) if Gm_m >= 0 else (dGm_m < 0)
        else:
            is_pos = sig_f > 0.0

        if is_pos:
            if not in_sig_lobe:
                sig_lobes += 1
                in_sig_lobe = True
            last_pos_sigma_t = tb
            Da, Db = abs(Ga), abs(Gb)
            if Db > Da:
                n_blp += Db - Da
                if Da >= eps_mp:
                    i_rhp += mp.log(Db / Da)
                elif Db <= eps_mp:
                    i_rhp += (Db - Da) / eps_mp
                else:
                    i_rhp += (eps_mp - Da) / eps_mp + mp.log(Db / eps_mp)
        else:
            in_sig_lobe = False

    dG_lobes = 0
    in_dG_lobe = False
    dG_pts = sorted([mp.mpf(0)] + exts_mp + [t_end_mp])
    max_dG_v = float(np.max(dG_f64))
    for idx in range(len(dG_pts) - 1):
        a_l, b_l = dG_pts[idx], dG_pts[idx + 1]
        if b_l - a_l <= mp.mpf("1e-10"):
            continue
        tm_f = float((a_l + b_l) / 2)
        _, dGm_f = eval_f64_scalar(tm_f)
        if need_mp_roots or abs(dGm_f) < 1e-8:
            dG_pos = fn_dG_mp((a_l + b_l) / 2) > 0
        else:
            dG_pos = dGm_f > 0.0
        if dG_pos:
            if not in_dG_lobe:
                dG_lobes += 1
                in_dG_lobe = True
                if dG_lobes == 1:
                    # Refine maximum of first positive dG lobe
                    phi_g = (math.sqrt(5.0) - 1.0) * 0.5
                    ca_f, cb_f = float(a_l), float(b_l)
                    x1_f = cb_f - phi_g * (cb_f - ca_f)
                    x2_f = ca_f + phi_g * (cb_f - ca_f)
                    fx1_f, fx2_f = eval_f64_scalar(x1_f)[1], eval_f64_scalar(x2_f)[1]
                    for _ in range(25):
                        if fx1_f < fx2_f:
                            ca_f, x1_f, fx1_f = x1_f, x2_f, fx2_f
                            x2_f = ca_f + phi_g * (cb_f - ca_f)
                            fx2_f = eval_f64_scalar(x2_f)[1]
                        else:
                            cb_f, x2_f, fx2_f = x2_f, x1_f, fx1_f
                            x1_f = cb_f - phi_g * (cb_f - ca_f)
                            fx1_f = eval_f64_scalar(x1_f)[1]
                    t_pk = x1_f if fx1_f > fx2_f else x2_f
                    max_dG_v = max(max_dG_v, float(fn_dG_mp(mp.mpf(str(t_pk)))))
        else:
            in_dG_lobe = False

    min_G = min(float(item[2]) for item in merged)
    return {
        "mu": mu_val,
        "g": g_val,
        "N_BLP": float(n_blp),
        "I_RHP_reg_eps1e3": float(i_rhp),
        "zero_crossings_G": len(zeros_mp),
        "dG_positive_lobes": dG_lobes,
        "sigma_BLP_positive_lobes": sig_lobes,
        "last_positive_sigma_t": float(last_pos_sigma_t),
        "leading_asymptotic_envelope_crossover_t": t_asymp,
        "has_non_invertible_singularity": bool(len(zeros_mp) > 0),
        "min_G": min_G,
        "max_dG": max_dG_v,
        "final_dG_at_tmax": float(dG_end),
        "t_max_used": t_end,
    }
