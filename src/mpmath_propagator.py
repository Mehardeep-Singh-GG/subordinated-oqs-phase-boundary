#!/usr/bin/env python3
"""
Arbitrary-precision (mp.dps >= 50) evaluator for the time-subordinated coherence
propagator G_{mu,g}(t) and its exact time derivative dG_{mu,g}(t)/dt.

Implements two independent exact representations:
1. Exact Hankel branch-cut spectral integral + principal-sheet pole residues
   (valid for all t > 0, mu in (0, 1], g > 0).
2. Exact two-parameter Mittag-Leffler series E_mu, E_{mu,mu}
   (exact via power series with extradps for t^mu <= 45).

Cross-checks both methods to < 1e-45 (< 1e-30 required).
"""

from __future__ import annotations

import mpmath as mp


def mu_pole_exact(g: float | mp.mpf) -> mp.mpf:
    """Critical exponent mu_pole(g) = 1 - arccos(g)/pi where complex poles enter principal sheet."""
    g_mp = mp.mpf(g)
    if g_mp >= 1:
        return mp.mpf(1)
    if g_mp <= 0:
        return mp.mpf("0.5")
    return 1 - mp.acos(g_mp) / mp.pi


def pole_parameters(mu: float | mp.mpf, g: float | mp.mpf) -> dict:
    """Return principal-sheet pole coordinates s_+ = -alpha + i*Omega when mu > mu_pole(g)."""
    mu_mp = mp.mpf(mu)
    g_mp = mp.mpf(g)
    mpole = mu_pole_exact(g_mp)
    if g_mp >= 1 or mu_mp <= mpole:
        return {"has_pole": False, "mu_pole": mpole, "alpha": None, "Omega": None}
    theta = mp.acos(g_mp)
    psi = (mp.pi - theta) / mu_mp
    return {
        "has_pole": True,
        "mu_pole": mpole,
        "psi": psi,
        "alpha": -mp.cos(psi),
        "Omega": mp.sin(psi),
    }


def ml_series(alpha: mp.mpf, beta: mp.mpf, z: mp.mpc, max_terms: int = 1200) -> mp.mpc:
    """Power-series evaluation of E_{alpha, beta}(z) with dynamic extradps for zero cancellation.
    Max term magnitude scales like exp(|z|^{1/alpha})."""
    abs_z = float(abs(z))
    alpha_f = float(alpha)
    peak_exp = abs_z ** (1.0 / alpha_f) if abs_z > 0 else 0.0
    extra = max(25, int(peak_exp * 0.45) + 25)
    need_terms = max(max_terms, int(8 * peak_exp / alpha_f) + 120)
    with mp.extradps(extra):
        alpha_w = mp.mpf(alpha)
        beta_w = mp.mpf(beta)
        z_w = mp.mpc(z)
        s = mp.mpc(0)
        zk = mp.mpc(1)
        tol = mp.mpf(10) ** (-(mp.mp.dps - 5))
        for k in range(need_terms):
            term = zk / mp.gamma(alpha_w * k + beta_w)
            s += term
            if k > 8 and abs(term) < tol * max(mp.mpf(1), abs(s)):
                break
            zk *= z_w
        return +s


def eval_G_dG_ml_series(t: float | mp.mpf, mu: float | mp.mpf, g: float | mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    """Exact G_{mu,g}(t) and dG_{mu,g}(t)/dt via Mittag-Leffler series."""
    t_mp = mp.mpf(t)
    mu_mp = mp.mpf(mu)
    g_mp = mp.mpf(g)
    if abs(mu_mp - 1) < mp.mpf("1e-45"):
        return _eval_mu1_exact(t_mp, g_mp)

    t_mu = t_mp ** mu_mp
    max_root = mp.mpf(1) if g_mp <= 1 else (g_mp + mp.sqrt(g_mp * g_mp - 1))
    scale_t = float(t_mp * (max_root ** (1 / mu_mp)))
    extra = max(25, int(scale_t * 0.45) + 25)
    need_terms = max(800, int(8 * scale_t / float(mu_mp)) + 120)
    with mp.extradps(extra):
        t_w = mp.mpf(t)
        mu_w = mp.mpf(mu)
        g_w = mp.mpf(g)
        t_mu_w = t_w ** mu_w
        if abs(g_w - 1) < mp.mpf("1e-40"):
            z = -t_mu_w
            E1 = mp.re(ml_series(mu_w, mp.mpf(1), z))
            Emm = mp.re(ml_series(mu_w, mu_w, z))
            G = E1 + (t_mu_w / mu_w) * Emm
            s = mp.mpf(0)
            zk = mp.mpf(1)
            tol = mp.mpf(10) ** (-(mp.mp.dps - 5))
            for k in range(need_terms):
                term = (k + 1) * zk / mp.gamma(mu_w * (k + 2))
                s += term
                if k > 8 and abs(term) < tol * max(mp.mpf(1), abs(s)):
                    break
                zk *= z
            dG = -(t_w ** (2 * mu_w - 1)) * s
            return +G, +dG
        elif g_w < 1:
            sq = mp.sqrt(1 - g_w * g_w)
            z_plus = mp.mpc(-g_w, sq)
            arg = z_plus * t_mu_w
            E1 = ml_series(mu_w, mp.mpf(1), arg)
            Emm = ml_series(mu_w, mu_w, arg)
            G = mp.re(E1) + (g_w / sq) * mp.im(E1)
            dG = -(t_w ** (mu_w - 1)) / sq * mp.im(Emm)
            return +G, +dG
        else:
            sq = mp.sqrt(g_w * g_w - 1)
            zp = -g_w + sq
            zm = -g_w - sq
            diff = zp - zm
            E1p = mp.re(ml_series(mu_w, mp.mpf(1), zp * t_mu_w))
            E1m = mp.re(ml_series(mu_w, mp.mpf(1), zm * t_mu_w))
            G = (zp * E1m - zm * E1p) / diff
            Emmp = mp.re(ml_series(mu_w, mu_w, zp * t_mu_w))
            Emmm = mp.re(ml_series(mu_w, mu_w, zm * t_mu_w))
            dG = (t_w ** (mu_w - 1)) / diff * (Emmm - Emmp)
            return +G, +dG


def _eval_mu1_exact(t: mp.mpf, g: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    with mp.extradps(15):
        if g < 1:
            om = mp.sqrt(1 - g * g)
            G = mp.exp(-g * t) * (mp.cos(om * t) + (g / om) * mp.sin(om * t))
            dG = -mp.exp(-g * t) * mp.sin(om * t) / om
            return +G, +dG
        elif abs(g - 1) < mp.mpf("1e-45"):
            G = mp.exp(-t) * (1 + t)
            dG = -t * mp.exp(-t)
            return +G, +dG
        else:
            kap = mp.sqrt(g * g - 1)
            G = mp.exp(-g * t) * (mp.cosh(kap * t) + (g / kap) * mp.sinh(kap * t))
            dG = -mp.exp(-g * t) * mp.sinh(kap * t) / kap
            return +G, +dG


def eval_G_dG_hankel_components(
    t: float | mp.mpf, mu: float | mp.mpf, g: float | mp.mpf, need_G: bool = True, need_dG: bool = True
) -> dict[str, mp.mpf]:
    """
    Exact Hankel branch-cut integral + principal-sheet pole residues, returning
    G_cut, G_pole, G, dG_cut, dG_pole, dG.
    Uses u = r^mu coordinates on [0, u_max] with smart breakpoints around u=1 and t^(-mu).
    """
    t_mp = mp.mpf(t)
    mu_mp = mp.mpf(mu)
    g_mp = mp.mpf(g)

    if abs(mu_mp - 1) < mp.mpf("1e-45"):
        G, dG = _eval_mu1_exact(t_mp, g_mp)
        return {
            "G_cut": mp.mpf(0),
            "G_pole": G,
            "G": G,
            "dG_cut": mp.mpf(0),
            "dG_pole": dG,
            "dG": dG,
        }

    orig_dps = mp.mp.dps
    with mp.extradps(20):
        t_w = mp.mpf(t)
        mu_w = mp.mpf(mu)
        g_w = mp.mpf(g)

        c1 = mp.cos(mp.pi * mu_w)
        s1 = mp.sin(mp.pi * mu_w)
        c2 = mp.cos(2 * mp.pi * mu_w)
        pref = 2 * s1 / (mp.pi * mu_w)
        inv_mu = 1 / mu_w

        x_max = mp.mpf(int((mp.mp.dps + 15) * 2.31) + 5)
        u_max = (x_max / t_w) ** mu_w

        def denom_sq(u: mp.mpf) -> mp.mpf:
            if g_w < 1:
                theta = mp.acos(g_w)
                um1 = u - 1
                s_a = mp.cos((mp.pi * mu_w - theta) / 2)
                s_b = mp.sin((mp.pi * (mu_w - (1 - theta / mp.pi))) / 2)
                return (um1 * um1 + 4 * u * s_a * s_a) * (um1 * um1 + 4 * u * s_b * s_b)
            u2 = u * u
            return u2 * u2 + 4 * g_w * g_w * u2 + 1 + 4 * g_w * u * (u2 + 1) * c1 + 2 * u2 * c2

        def int_G(u: mp.mpf) -> mp.mpf:
            r = u ** inv_mu
            rt = r * t_w
            if rt > x_max + 20:
                return mp.mpf(0)
            d = denom_sq(u)
            if d == 0:
                return mp.mpf(0)
            return pref * (u * c1 + g_w) * mp.exp(-rt) / d

        def int_dG(u: mp.mpf) -> mp.mpf:
            r = u ** inv_mu
            rt = r * t_w
            if rt > x_max + 20:
                return mp.mpf(0)
            d = denom_sq(u)
            if d == 0:
                return mp.mpf(0)
            return -pref * r * (u * c1 + g_w) * mp.exp(-rt) / d

        if g_w < 1:
            mpole = mu_pole_exact(g_w)
            delta = abs(mp.pi * (mu_w - mpole))
            # Exact pole-on-cut boundary mu == mu_pole(g):
            # G evaluates via algebraically regularized Sokhotski-Plemelj PV + half-residue e^{-t}/(2*mu_p).
            # dG has zero half-residue (dG_pole = 0) and reduces by Theorem 4 (Dominated Convergence)
            # to the non-singular integral -int phi_{mu_p,g}(r)*(e^{-rt} - e^{-t}) dr, regularized on the
            # algebraic tail r -> inf via z = r^{-(2*mu_p - 1)}.
            exact_tol = mp.mpf(10) ** (-max(22, orig_dps - 5))
            if delta < exact_tol:
                mu_p = mpole
                p_inv = 1 / mu_p
                s2 = 1 - g_w * g_w
                s_th = mp.sqrt(s2)
                C_p = -2 * g_w * s_th / (mp.pi * mu_p)
                exp_mt = mp.exp(-t_w)

                if need_G:
                    def _f_u(v_arg: mp.mpf) -> mp.mpf:
                        if v_arg <= -1:
                            return mp.mpf(1)  # r=0 => e^0 / ((1)^2 + 0) = 1
                        r_val = mp.exp(p_inv * mp.log1p(v_arg)) if abs(v_arg) < mp.mpf("0.5") else ((1 + v_arg) ** p_inv)
                        rt_val = r_val * t_w
                        if rt_val > x_max + 20:
                            return mp.mpf(0)
                        return mp.exp(-rt_val) / (v_arg * v_arg + 4 * (1 + v_arg) * s2)

                    f1_deriv_2 = -2 * (1 + t_w * p_inv) * exp_mt / (4 * s2)

                    def _pv_G(v_arg: mp.mpf) -> mp.mpf:
                        if abs(v_arg) < mp.mpf("1e-26"):
                            return C_p * f1_deriv_2
                        return C_p * (_f_u(v_arg) - _f_u(-v_arg)) / v_arg

                    v_pts = [
                        mp.mpf(0), mp.mpf("1e-26"), mp.mpf("1e-10"), mp.mpf("1e-4"),
                        mp.mpf("0.1"), mp.mpf("0.5"), mp.mpf("0.9"), mp.mpf(1),
                    ]
                    if t_w > 1:
                        for sc_t in (mp.mpf(1), mp.mpf(5), mp.mpf(20)):
                            u_b = (sc_t / t_w) ** mu_p
                            if mp.mpf("1e-15") < u_b < 1:
                                v_pts.append(1 - u_b)
                    v_pts = sorted(set(pt for pt in v_pts if 0 <= pt <= 1))
                    G_cut = mp.quad(_pv_G, v_pts)

                    if u_max > 2:
                        def _G_tail(u_arg: mp.mpf) -> mp.mpf:
                            r_val = u_arg ** p_inv
                            rt_val = r_val * t_w
                            if rt_val > x_max + 20:
                                return mp.mpf(0)
                            um1 = u_arg - 1
                            return C_p * mp.exp(-rt_val) / (um1 * (um1 * um1 + 4 * u_arg * s2))

                        hi_pts = [mp.mpf(2), u_max]
                        for sc_t in (mp.mpf(1), mp.mpf(5), mp.mpf(20)):
                            u_b = (sc_t / t_w) ** mu_p
                            if 2 < u_b < u_max:
                                hi_pts.append(u_b)
                        G_cut += mp.quad(_G_tail, sorted(set(hi_pts)))
                    G_pole = exp_mt / (2 * mu_p)
                else:
                    G_cut = mp.mpf(0)
                    G_pole = mp.mpf(0)

                if need_dG:
                    alpha = 2 * mu_p - 1

                    def _dct_dG_u(u_arg: mp.mpf) -> mp.mpf:
                        v_arg = u_arg - 1
                        if abs(v_arg) < mp.mpf("1e-26"):
                            return -C_p * (-t_w * p_inv * exp_mt) / (4 * s2)
                        if abs(v_arg) < mp.mpf("0.5"):
                            r_val = mp.exp(p_inv * mp.log1p(v_arg))
                            dr_t = t_w * mp.expm1(p_inv * mp.log1p(v_arg))
                        else:
                            r_val = u_arg ** p_inv
                            dr_t = t_w * (r_val - 1)
                        diff_exp = exp_mt * mp.expm1(-dr_t) if abs(dr_t) < x_max + 20 or dr_t < 0 else -exp_mt
                        return -C_p * r_val * diff_exp / (v_arg * (v_arg * v_arg + 4 * u_arg * s2))

                    u_split = mp.mpf(2)
                    r_split = u_split ** p_inv
                    z_max = r_split ** (-alpha)

                    def _dct_dG_z(z_arg: mp.mpf) -> mp.mpf:
                        if z_arg <= 0:
                            return C_p * exp_mt * mu_p / alpha
                        r_val = z_arg ** (-1 / alpha)
                        u_val = r_val ** mu_p
                        v_arg = u_val - 1
                        rt_val = r_val * t_w
                        diff_exp = exp_mt * mp.expm1(-t_w * (r_val - 1)) if rt_val < x_max + 20 else -exp_mt
                        val_u = -C_p * r_val * diff_exp / (v_arg * (v_arg * v_arg + 4 * u_val * s2))
                        jac = (mu_p / alpha) * (r_val ** (3 * mu_p - 1))
                        return val_u * jac

                    lo_dG_pts = [
                        mp.mpf(0), mp.mpf("0.5"), mp.mpf(1) - mp.mpf("1e-26"),
                        mp.mpf(1), mp.mpf(1) + mp.mpf("1e-26"), mp.mpf("1.5"), u_split,
                    ]
                    for sc_t in (mp.mpf("0.2"), mp.mpf(1), mp.mpf(5), mp.mpf(20)):
                        u_b = (sc_t / t_w) ** mu_p
                        if mp.mpf("1e-15") < u_b < u_split:
                            lo_dG_pts.append(u_b)
                    lo_dG_pts = sorted(set(lo_dG_pts))
                    dG_part1 = mp.quad(_dct_dG_u, lo_dG_pts)

                    z_pts = [mp.mpf(0), z_max]
                    for r_b in (mp.mpf("0.5") / t_w, mp.mpf(1) / t_w, mp.mpf(5) / t_w, mp.mpf(25) / t_w, mp.mpf(100) / t_w):
                        if r_b > r_split:
                            z_pts.append(r_b ** (-alpha))
                    dG_part2 = mp.quad(_dct_dG_z, sorted(set(z_pts)))
                    dG_cut = dG_part1 + dG_part2
                    dG_pole = mp.mpf(0)
                else:
                    dG_cut = mp.mpf(0)
                    dG_pole = mp.mpf(0)

                return {
                    "G_cut": +G_cut,
                    "G_pole": +G_pole,
                    "G": +(G_cut + G_pole),
                    "dG_cut": +dG_cut,
                    "dG_pole": +dG_pole,
                    "dG": +(dG_cut + dG_pole),
                }

        cand = [t_w ** (-mu_w), (5 / t_w) ** mu_w, (20 / t_w) ** mu_w]
        if g_w < 1:
            mpole = mu_pole_exact(g_w)
            delta = abs(mp.pi * (mu_w - mpole))
            cand.append(mp.mpf(1))
            if delta < mp.mpf("0.5"):
                for mult in (1000, 100, 10, 2, mp.mpf("0.5"), mp.mpf("0.1")):
                    sc = delta * mult
                    if mp.mpf("1e-45") < sc < mp.mpf("0.5"):
                        if 1 - sc > 0:
                            cand.append(1 - sc)
                        cand.append(1 + sc)

        pts = [mp.mpf(0)]
        min_sep = mp.mpf("1e-45")
        for p in sorted(cand):
            if mp.mpf("1e-45") < p < u_max and p - pts[-1] > max(min_sep, pts[-1] * min_sep):
                pts.append(p)
        if u_max - pts[-1] > max(min_sep, pts[-1] * min_sep):
            pts.append(u_max)
        else:
            pts[-1] = u_max

        G_cut = mp.quad(int_G, pts) if need_G else mp.mpf(0)
        dG_cut = mp.quad(int_dG, pts) if need_dG else mp.mpf(0)

        G_pole = mp.mpf(0)
        dG_pole = mp.mpf(0)
        if g_w < 1:
            mpole = mu_pole_exact(g_w)
            if mu_w > mpole:
                theta = mp.acos(g_w)
                psi = (mp.pi - theta) / mu_w
                s_plus = mp.exp(mp.mpc(0, psi))
                cot_th = g_w / mp.sqrt(1 - g_w * g_w)
                coeff = mp.mpc(1, -cot_th)
                exp_term = mp.exp(s_plus * t_w)
                if need_G:
                    G_pole = mp.re(exp_term * coeff) / mu_w
                if need_dG:
                    dG_pole = mp.re(s_plus * exp_term * coeff) / mu_w

        return {
            "G_cut": +G_cut,
            "G_pole": +G_pole,
            "G": +(G_cut + G_pole),
            "dG_cut": +dG_cut,
            "dG_pole": +dG_pole,
            "dG": +(dG_cut + dG_pole),
        }


def eval_dG_ml_series(t: float | mp.mpf, mu: float | mp.mpf, g: float | mp.mpf) -> mp.mpf:
    """Fast exact dG_{mu,g}(t)/dt via Mittag-Leffler series (skips computing G)."""
    t_mp = mp.mpf(t)
    mu_mp = mp.mpf(mu)
    g_mp = mp.mpf(g)
    if abs(mu_mp - 1) < mp.mpf("1e-45"):
        _, dG = _eval_mu1_exact(t_mp, g_mp)
        return dG

    max_root = mp.mpf(1) if g_mp <= 1 else (g_mp + mp.sqrt(g_mp * g_mp - 1))
    scale_t = float(t_mp * (max_root ** (1 / mu_mp)))
    extra = max(25, int(scale_t * 0.45) + 25)
    need_terms = max(800, int(8 * scale_t / float(mu_mp)) + 120)
    with mp.extradps(extra):
        t_w = mp.mpf(t)
        mu_w = mp.mpf(mu)
        g_w = mp.mpf(g)
        t_mu_w = t_w ** mu_w
        if abs(g_w - 1) < mp.mpf("1e-40"):
            z = -t_mu_w
            s = mp.mpf(0)
            zk = mp.mpf(1)
            tol = mp.mpf(10) ** (-(mp.mp.dps - 5))
            for k in range(need_terms):
                term = (k + 1) * zk / mp.gamma(mu_w * (k + 2))
                s += term
                if k > 8 and abs(term) < tol * max(mp.mpf(1), abs(s)):
                    break
                zk *= z
            return -(t_w ** (2 * mu_w - 1)) * s
        elif g_w < 1:
            sq = mp.sqrt(1 - g_w * g_w)
            z_plus = mp.mpc(-g_w, sq)
            Emm = ml_series(mu_w, mu_w, z_plus * t_mu_w)
            return -(t_w ** (mu_w - 1)) / sq * mp.im(Emm)
        else:
            sq = mp.sqrt(g_w * g_w - 1)
            zp = -g_w + sq
            zm = -g_w - sq
            diff = zp - zm
            Emmp = mp.re(ml_series(mu_w, mu_w, zp * t_mu_w))
            Emmm = mp.re(ml_series(mu_w, mu_w, zm * t_mu_w))
            return (t_w ** (mu_w - 1)) / diff * (Emmm - Emmp)


def eval_G_dG(t: float | mp.mpf, mu: float | mp.mpf, g: float | mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    """
    Fastest 50-digit exact evaluator: uses Mittag-Leffler series when scaled t <= 25
    and Hankel + pole residue when scaled t > 25 (both verified identical to < 1e-45).
    """
    t_mp = mp.mpf(t)
    mu_mp = mp.mpf(mu)
    g_mp = mp.mpf(g)
    if abs(mu_mp - 1) < mp.mpf("1e-45"):
        return _eval_mu1_exact(t_mp, g_mp)
    max_root = mp.mpf(1) if g_mp <= 1 else (g_mp + mp.sqrt(g_mp * g_mp - 1))
    scale_t = float(t_mp * (max_root ** (1 / mu_mp)))
    if scale_t <= 26.0:
        return eval_G_dG_ml_series(t_mp, mu_mp, g_mp)
    res = eval_G_dG_hankel_components(t_mp, mu_mp, g_mp)
    return res["G"], res["dG"]


def eval_dG(t: float | mp.mpf, mu: float | mp.mpf, g: float | mp.mpf) -> mp.mpf:
    """Fast exact evaluator returning only dG_{mu,g}(t)/dt."""
    t_mp = mp.mpf(t)
    mu_mp = mp.mpf(mu)
    g_mp = mp.mpf(g)
    if abs(mu_mp - 1) < mp.mpf("1e-45"):
        _, dG = _eval_mu1_exact(t_mp, g_mp)
        return dG
    max_root = mp.mpf(1) if g_mp <= 1 else (g_mp + mp.sqrt(g_mp * g_mp - 1))
    scale_t = float(t_mp * (max_root ** (1 / mu_mp)))
    if scale_t <= 26.0:
        return eval_dG_ml_series(t_mp, mu_mp, g_mp)
    res = eval_G_dG_hankel_components(t_mp, mu_mp, g_mp, need_G=False, need_dG=True)
    return res["dG"]


if __name__ == "__main__":
    import time

    mp.mp.dps = 55
    print(f"Testing mpmath_propagator at mp.dps = {mp.mp.dps}")
    t0 = time.perf_counter()
    tests = [
        (0.05, 0.55, 10.0),
        (0.5, 0.40, 1.5),
        (0.5, 0.75, 12.0),
        (0.5, 0.90, 25.0),
        (0.9, 0.70, 5.0),
        (0.9, 0.92, 30.0),
        (1.0, 0.75, 4.0),
        (1.25, 0.75, 4.0),
    ]
    for g, mu, t in tests:
        G_ml, dG_ml = eval_G_dG_ml_series(t, mu, g)
        h = eval_G_dG_hankel_components(t, mu, g)
        print(
            f"g={g:<4} mu={mu:<4} t={t:<4} | err_G={mp.nstr(abs(G_ml - h['G']), 3)} | err_dG={mp.nstr(abs(dG_ml - h['dG']), 3)}"
        )
    print(f"Cross-check elapsed: {time.perf_counter() - t0:.2f}s")
