#!/usr/bin/env python3
"""
Compute the exact zero-crossing / non-invertibility threshold mu_zero(g) where
G_{mu,g}(t_touch) = 0 and dG_{mu,g}(t_touch)/dt = 0 simultaneously, using
65-digit 2D Newton iteration on (G, dG) = (0, 0) with verified residuals < 1e-55.

For mu_crit(g) < mu < mu_zero(g): backflow occurs (N_BLP > 0, not P/CP-divisible)
while Phi_t remains strictly invertible everywhere (G_{mu,g}(t) > 0) and unregularized
I_RHP < infinity. For mu >= mu_zero(g): G_{mu,g}(t) touches/crosses zero and Phi_t
loses invertibility.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path

import mpmath as mp
import numpy as np

from mpmath_propagator import eval_G_dG, mu_pole_exact

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"


def scout_mu_zero(g_val: float) -> tuple[float, float]:
    """Dense fast scout for (mu_zero, t_touch) at dps=18."""
    mp.mp.dps = 18
    g_mp = mp.mpf(str(g_val))
    theta = math.acos(g_val)
    mpole = 1.0 - theta / math.pi
    om = math.sqrt(max(1e-6, 1.0 - g_val * g_val))
    # First minimum of G occurs near t ~ pi / om (strictly < 2*pi/om)
    t_lo = max(1.0, 0.5 * math.pi / om)
    t_hi = min(40.0, 2.2 * math.pi / om)
    ts = np.linspace(t_lo, t_hi, 120)

    def min_G(mu_f: float) -> tuple[float, float]:
        mu_mp = mp.mpf(str(mu_f))
        vals = [float(eval_G_dG(mp.mpf(str(tv)), mu_mp, g_mp)[0]) for tv in ts]
        idx = int(np.argmin(vals))
        return vals[idx], float(ts[idx])

    a = mpole + 1e-3
    b = 0.999995
    vb, tb = min_G(b)
    assert vb < 0.0, f"No zero crossing found at g={g_val}, mu={b}: min G={vb}"
    for _ in range(22):
        mid = 0.5 * (a + b)
        vm, tm = min_G(mid)
        if vm < 0.0:
            b = mid
            tb = tm
        else:
            a = mid
    return 0.5 * (a + b), tb


def find_mu_zero_newton(g_val: float, work_dps: int = 75) -> dict:
    """Solve G(t, mu) = 0, dG/dt(t, mu) = 0 to >55 exact digits via 2D Newton."""
    mu_init, t_init = scout_mu_zero(g_val)
    mp.mp.dps = work_dps
    g_mp = mp.mpf(str(g_val))
    mu_mp = mp.mpf(repr(float(mu_init)))
    t_mp = mp.mpf(repr(float(t_init)))
    mpole = mu_pole_exact(g_mp)

    h_t = mp.mpf("1e-22")
    h_mu = min(mp.mpf("1e-22"), (1 - mu_mp) / 1000)

    for it in range(20):
        F1, F2 = eval_G_dG(t_mp, mu_mp, g_mp)
        res = max(abs(F1), abs(F2))
        if res < mp.mpf("1e-62"):
            break
        h_mu = min(mp.mpf("1e-22"), (1 - mu_mp) / 1000, (mu_mp - mpole) / 1000)
        # Central-difference Jacobian at 75-digit precision (accurate to ~1e-45)
        Gp_t, dGp_t = eval_G_dG(t_mp + h_t, mu_mp, g_mp)
        Gm_t, dGm_t = eval_G_dG(t_mp - h_t, mu_mp, g_mp)
        Gp_m, dGp_m = eval_G_dG(t_mp, mu_mp + h_mu, g_mp)
        Gm_m, dGm_m = eval_G_dG(t_mp, mu_mp - h_mu, g_mp)

        J11 = (Gp_t - Gm_t) / (2 * h_t)
        J21 = (dGp_t - dGm_t) / (2 * h_t)
        J12 = (Gp_m - Gm_m) / (2 * h_mu)
        J22 = (dGp_m - dGm_m) / (2 * h_mu)

        det = J11 * J22 - J12 * J21
        dt = -(J22 * F1 - J12 * F2) / det
        dmu = -(-J21 * F1 + J11 * F2) / det

        # Damping guard to stay inside (mpole, 1) and t > 0
        step = mp.mpf(1)
        while (mu_mp + step * dmu >= 1) or (mu_mp + step * dmu <= mpole) or (t_mp + step * dt <= 0):
            step *= mp.mpf("0.5")
        t_mp += step * dt
        mu_mp += step * dmu

    F1, F2 = eval_G_dG(t_mp, mu_mp, g_mp)
    assert abs(F1) < mp.mpf("1e-55") and abs(F2) < mp.mpf("1e-55"), (
        f"Newton failed at g={g_val}: |G|={abs(F1)}, |dG|={abs(F2)}"
    )
    return {
        "g": g_val,
        "mu_zero": mp.nstr(mu_mp, 25),
        "t_zero_touch": mp.nstr(t_mp, 20),
        "residual_G": mp.nstr(abs(F1), 6),
        "residual_dG": mp.nstr(abs(F2), 6),
    }


if __name__ == "__main__":
    t0 = time.perf_counter()
    g_list = [0.05, 0.10, 0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.75, 0.80, 0.85, 0.90, 0.95]
    rows = []
    for gv in g_list:
        r = find_mu_zero_newton(gv)
        rows.append(r)
        print(
            f"g={gv:4.2f} | mu_zero={r['mu_zero'][:18]} | t_touch={r['t_zero_touch'][:12]} "
            f"| res=({r['residual_G']}, {r['residual_dG']})",
            flush=True,
        )
    with open(DATA_DIR / "mu_zero_boundary.json", "w", encoding="utf-8") as f:
        json.dump(rows, f, indent=2, allow_nan=False)
    print(f"Elapsed: {time.perf_counter() - t0:.1f}s", flush=True)
