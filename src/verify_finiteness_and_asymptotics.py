#!/usr/bin/env python3
"""
Verify:
1. Finiteness of backflow intervals and zero crossings of G_{mu,g}(t) for mu < 1
   (since G_pole decays exponentially while dG_cut ~ -C t^{-(mu+1)} algebraically).
2. Asymptotic formula for g -> 1^-:
     1 - mu_crit(g) ~ (pi^2 / (2 * e * (1 - g^2))) * exp(-pi*g / sqrt(1 - g^2))
   (and two-term Watson refinement Eq. (19)) against exact 55-digit data.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
import pandas as pd

from blp_exact_helper import compute_exact_nblp_and_rhp
from mpmath_propagator import eval_G_dG, eval_G_dG_hankel_components

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"


def count_backflow_lobes(mu_val: float, g_val: float, t_max: float | None = None) -> dict:
    """Compute exact zero-crossings of G, positive backflow lobes, and N_BLP via Proposition 1(b)."""
    res = compute_exact_nblp_and_rhp(mu_val, g_val, t_max=t_max)
    return {
        "mu": mu_val,
        "g": g_val,
        "zero_crossings_G": res["zero_crossings_G"],
        "dG_positive_lobes": res["dG_positive_lobes"],
        "sigma_BLP_positive_lobes": res["sigma_BLP_positive_lobes"],
        "last_positive_sigma_t": res["last_positive_sigma_t"],
        "leading_asymptotic_envelope_crossover_t": res["leading_asymptotic_envelope_crossover_t"],
        "N_BLP": res["N_BLP"],
        "I_RHP_reg_eps1e3": res["I_RHP_reg_eps1e3"],
        "final_dG_at_tmax": res["final_dG_at_tmax"],
        "t_max_used": res["t_max_used"],
    }


def main():
    # 1. Finite backflow lobes for g=0.50 as mu approaches 1
    lobe_rows = []
    for mu_val in [0.80, 0.85, 0.90, 0.95, 0.98]:
        r = count_backflow_lobes(mu_val, 0.50)
        lobe_rows.append(r)
        t_cross = r["leading_asymptotic_envelope_crossover_t"] or 0.0
        print(
            f"g=0.50, mu={mu_val:.2f}: zeros={r['zero_crossings_G']}, "
            f"sigma_lobes={r['sigma_BLP_positive_lobes']}, last_pos_t={r['last_positive_sigma_t']:.4f}, "
            f"t_asymp={t_cross:.4f}, N_BLP={r['N_BLP']:.8f}",
            flush=True,
        )

    # 2. Check asymptotic ratio against leading g->1^- law and two-term Watson refinement
    df_b = pd.read_csv(DATA_DIR / "phase_boundary_exact.csv")
    asymp_rows = []
    for _, row in df_b[df_b["g"] < 1.0].iterrows():
        g = float(row["g"])
        if g < 0.70:
            continue
        one_minus = float(row["one_minus_mu_crit"])
        om = math.sqrt(1.0 - g * g)
        t1_exact = (math.pi + math.acos(g)) / om
        pred_leading = (math.pi ** 2 / (2.0 * math.e * (1.0 - g ** 2))) * math.exp(-math.pi * g / om)
        pred_exact_t1 = (t1_exact ** 2 / (2.0 * g)) * math.exp(-g * t1_exact)
        pred_watson2 = (t1_exact ** 2 / (2.0 * g + 4.0 * (4.0 * g * g - 1.0) / t1_exact)) * math.exp(-g * t1_exact)
        asymp_rows.append({
            "g": g,
            "one_minus_mu_crit": one_minus,
            "pred_leading_g1": pred_leading,
            "ratio_leading_g1": one_minus / pred_leading,
            "pred_exact_t1": pred_exact_t1,
            "ratio_exact_t1": one_minus / pred_exact_t1,
            "pred_watson2": pred_watson2,
            "ratio_watson2": one_minus / pred_watson2,
        })
        print(
            f"g={g:4.2f}: 1-mu_c={one_minus:.6e} | pred_watson2={pred_watson2:.6e} | ratio={one_minus/pred_watson2:.4f}",
            flush=True,
        )

    out = {"finite_backflow_lobes": lobe_rows, "asymptotic_g_to_1": asymp_rows}
    with open(DATA_DIR / "finiteness_and_asymptotics.json", "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
    print("Saved finiteness_and_asymptotics.json", flush=True)


if __name__ == "__main__":
    main()
