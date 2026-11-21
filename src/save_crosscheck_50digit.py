#!/usr/bin/env python3
"""
Systematic 55-digit cross-check of Hankel branch-cut + pole residue evaluation
against exact two-parameter Mittag-Leffler series E_mu, E_{mu,mu} across all regimes:
  - Complete monotonicity (mu <= 0.5)
  - Pole-free non-CM wedge (0.5 < mu <= mu_pole(g))
  - Buffer wedge (mu_pole(g) < mu <= mu_crit(g))
  - Non-Markovian backflow (mu > mu_crit(g))
  - Exceptional point g = 1.0
  - Overdamped g > 1.0
Saves full 50-digit table to data/crosscheck_50digit.json.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp

from mpmath_propagator import eval_G_dG_hankel_components, eval_G_dG_ml_series, mu_pole_exact

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def main():
    mp.mp.dps = 70
    cases = [
        (0.20, 0.40, 2.5, "CM (mu <= 0.5)"),
        (0.50, 0.50, 4.0, "CM boundary (mu = 0.5)"),
        (0.50, 0.65, 3.0, "Pole-free CP-Div (0.5 < mu <= mu_pole)"),
        (0.50, "mu_pole", 1.0, "Pole-entry boundary (mu = mu_pole = 2/3)"),
        (0.50, 0.75, 6.2, "Buffer CP-Div (mu_pole < mu <= mu_crit)"),
        (0.50, 0.90, 5.0, "Backflow (mu > mu_crit)"),
        (0.90, 0.80, 4.0, "Pole-free high-g (mu < mu_pole)"),
        (0.90, 0.92, 9.0, "Buffer high-g (mu_pole < mu <= mu_crit)"),
        (0.95, 0.9995, 11.4, "Near-Markovian backflow (g=0.95, mu > mu_crit)"),
        (1.00, 0.75, 3.5, "Exceptional Point g = 1.0"),
        (1.25, 0.75, 3.5, "Overdamped g > 1.0"),
    ]
    rows = []
    max_err_G = mp.mpf(0)
    max_err_dG = mp.mpf(0)
    for g_val, mu_val, t_val, label in cases:
        g_mp = mp.mpf(str(g_val))
        if mu_val == "mu_pole":
            mu_mp = mu_pole_exact(g_mp)
            mu_out = float(mu_mp)
        else:
            mu_mp = mp.mpf(str(mu_val))
            mu_out = mu_val
        t_mp = mp.mpf(str(t_val))
        G_ml, dG_ml = eval_G_dG_ml_series(t_mp, mu_mp, g_mp)
        h = eval_G_dG_hankel_components(t_mp, mu_mp, g_mp)
        err_G = abs(G_ml - h["G"])
        err_dG = abs(dG_ml - h["dG"])
        if err_G > max_err_G:
            max_err_G = err_G
        if err_dG > max_err_dG:
            max_err_dG = err_dG
        rows.append({
            "regime": label,
            "g": g_val,
            "mu": mu_out,
            "mu_exact_str": "mu_pole(0.5)=2/3" if mu_val == "mu_pole" else str(mu_val),
            "t": t_val,
            "mu_pole": mp.nstr(mu_pole_exact(g_mp), 15),
            "G_ml_50d": mp.nstr(G_ml, 50),
            "G_hankel_50d": mp.nstr(h["G"], 50),
            "dG_ml_50d": mp.nstr(dG_ml, 50),
            "dG_hankel_50d": mp.nstr(h["dG"], 50),
            "G_cut": mp.nstr(h["G_cut"], 20),
            "G_pole": mp.nstr(h["G_pole"], 20),
            "dG_cut": mp.nstr(h["dG_cut"], 20),
            "dG_pole": mp.nstr(h["dG_pole"], 20),
            "abs_err_G": mp.nstr(err_G, 6),
            "abs_err_dG": mp.nstr(err_dG, 6),
        })
        print(f"{label:<45} | err_G={mp.nstr(err_G, 3)} | err_dG={mp.nstr(err_dG, 3)}", flush=True)

    out = {
        "working_dps": 70,
        "max_abs_err_G": mp.nstr(max_err_G, 6),
        "max_abs_err_dG": mp.nstr(max_err_dG, 6),
        "cases": rows,
    }
    out_path = DATA_DIR / "crosscheck_50digit.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
    print(f"Saved {out_path} (max_err_G={mp.nstr(max_err_G, 3)}, max_err_dG={mp.nstr(max_err_dG, 3)})", flush=True)


if __name__ == "__main__":
    main()
