#!/usr/bin/env python3
"""Quick 50-digit mpmath prototype to test Hankel+Pole vs Mittag-Leffler series
and investigate mu_crit(g) vs mu_pole(g)."""

import mpmath as mp

mp.mp.dps = 60  # working precision 60 digits to guarantee >50 accurate digits


def ml_series(alpha, beta, z, max_terms=500):
    """Direct series evaluation of E_{alpha, beta}(z) at current mp.dps."""
    # Use high internal dps to defeat cancellation for |z| up to ~60
    with mp.extradps(40):
        alpha = mp.mpf(alpha)
        beta = mp.mpf(beta)
        z = mp.mpc(z)
        s = mp.mpc(0)
        zk = mp.mpc(1)
        tol = mp.mpf(10) ** (-(mp.mp.dps - 5))
        for k in range(max_terms):
            term = zk / mp.gamma(alpha * k + beta)
            s += term
            if k > 5 and abs(term) < tol * max(mp.mpf(1), abs(s)):
                break
            zk *= z
        return +s


def G_and_dG_ml_series(t, mu, g):
    """Exact G_{mu,g}(t) and dG_{mu,g}(t)/dt via Mittag-Leffler series (valid for moderate t)."""
    with mp.extradps(40):
        t = mp.mpf(t)
        mu = mp.mpf(mu)
        g = mp.mpf(g)
        t_mu = t ** mu
        if abs(g - 1) < mp.mpf("1e-40"):
            z = -t_mu
            E1 = mp.re(ml_series(mu, 1, z))
            Emm = mp.re(ml_series(mu, mu, z))
            G = E1 + (t_mu / mu) * Emm
            # Exact series for -dG/dt = sum_{k=0}^\infty (k+1) (-1)^k t^{mu*(k+2)-1} / Gamma(mu*(k+2))
            s = mp.mpf(0)
            zk = mp.mpf(1)
            tol = mp.mpf(10) ** (-(mp.mp.dps - 5))
            for k in range(500):
                term = (k + 1) * zk / mp.gamma(mu * (k + 2))
                s += term
                if k > 5 and abs(term) < tol * max(mp.mpf(1), abs(s)):
                    break
                zk *= z
            dG = -(t ** (2 * mu - 1)) * s
            return +G, +dG
        elif g < 1:
            sq = mp.sqrt(1 - g * g)
            z_plus = mp.mpc(-g, sq)
            arg = z_plus * t_mu
            E1 = ml_series(mu, 1, arg)
            Emm = ml_series(mu, mu, arg)
            G = mp.re(E1) + (g / sq) * mp.im(E1)
            dG = -(t ** (mu - 1)) / sq * mp.im(Emm)
            return +G, +dG
        else:
            sq = mp.sqrt(g * g - 1)
            zp = -g + sq
            zm = -g - sq
            diff = zp - zm
            E1p = mp.re(ml_series(mu, 1, zp * t_mu))
            E1m = mp.re(ml_series(mu, 1, zm * t_mu))
            G = (zp * E1m - zm * E1p) / diff
            Emmp = mp.re(ml_series(mu, mu, zp * t_mu))
            Emmm = mp.re(ml_series(mu, mu, zm * t_mu))
            dG = (t ** (mu - 1)) / diff * (Emmm - Emmp)
            return +G, +dG


def mu_pole_exact(g):
    g = mp.mpf(g)
    if g >= 1:
        return mp.mpf(1)
    return 1 - mp.acos(g) / mp.pi


def G_and_dG_hankel(t, mu, g):
    """Exact Hankel branch-cut integral + principal-sheet pole residues in u = r^mu coordinates."""
    with mp.extradps(30):
        t = mp.mpf(t)
        mu = mp.mpf(mu)
        g = mp.mpf(g)

        if abs(mu - 1) < mp.mpf("1e-45"):
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

        c1 = mp.cos(mp.pi * mu)
        s1 = mp.sin(mp.pi * mu)
        c2 = mp.cos(2 * mp.pi * mu)
        pref = 2 * s1 / (mp.pi * mu)
        inv_mu = 1 / mu

        # Use u = r^mu so r = u^(1/mu) and K(r) dr = pref * (u*c1 + g) / |D|^2 du
        def denom_sq(u):
            u2 = u * u
            return u2 * u2 + 4 * g * g * u2 + 1 + 4 * g * u * (u2 + 1) * c1 + 2 * u2 * c2

        def int_G(u):
            r = u ** inv_mu
            rt = r * t
            if rt > 300:
                return mp.mpf(0)
            return pref * (u * c1 + g) * mp.exp(-rt) / denom_sq(u)

        def int_dG(u):
            r = u ** inv_mu
            rt = r * t
            if rt > 300:
                return mp.mpf(0)
            return -pref * r * (u * c1 + g) * mp.exp(-rt) / denom_sq(u)

        # Build smart breakpoints: around u=1 (near pole) and exponential decay scale u_cut ~ (250/t)^mu
        pts = [mp.mpf(0)]
        u_max = (mp.mpf(220) / t) ** mu
        # Ensure we split near u=1 if 1 < u_max and g < 1
        near_pts = []
        if g < 1:
            mpole = mu_pole_exact(g)
            delta = abs(mp.pi * (mu - mpole))
            # Add nodes around u=1 proportional to delta if delta is small
            if delta < mp.mpf("0.5"):
                for scale in [delta * 10, delta, delta / 10]:
                    if scale > mp.mpf("1e-20"):
                        if 1 - scale > 0:
                            near_pts.append(1 - scale)
                        near_pts.append(1 + scale)
            near_pts.append(mp.mpf(1))
        # Also add r*t ~ 1 scale -> u ~ t^(-mu)
        u_decay = t ** (-mu)
        for p in sorted(set(near_pts + [u_decay, u_decay * 10, mp.mpf(1)])):
            if mp.mpf("1e-30") < p < u_max:
                pts.append(p)
        pts.append(u_max)

        G_cut = mp.quad(int_G, pts)
        dG_cut = mp.quad(int_dG, pts)

        G_pole = mp.mpf(0)
        dG_pole = mp.mpf(0)
        if g < 1:
            mpole = mu_pole_exact(g)
            if mu > mpole:
                theta = mp.acos(g)
                psi = (mp.pi - theta) / mu
                s_plus = mp.exp(mp.mpc(0, psi))
                cot_th = g / mp.sqrt(1 - g * g)
                coeff = mp.mpc(1, -cot_th)
                exp_term = mp.exp(s_plus * t)
                G_pole = mp.re(exp_term * coeff) / mu
                dG_pole = mp.re(s_plus * exp_term * coeff) / mu

        return +(G_cut + G_pole), +(dG_cut + dG_pole)


print("=== Cross-check Hankel+Pole vs Mittag-Leffler series (mp.dps=60) ===")
for g, mu, t in [
    (0.5, 0.4, 1.5),
    (0.5, 0.75, 2.0),
    (0.5, 0.9, 5.0),
    (0.9, 0.7, 3.0),
    (0.9, 0.92, 8.0),
    (1.0, 0.75, 2.5),
    (1.25, 0.75, 2.5),
]:
    G1, dG1 = G_and_dG_ml_series(t, mu, g)
    G2, dG2 = G_and_dG_hankel(t, mu, g)
    print(
        f"g={g}, mu={mu}, t={t}: |dG_err|={float(abs(G1-G2)):.2e}, |ddG_err|={float(abs(dG1-dG2)):.2e}"
    )

print("\n=== Probing mu just above mu_pole(g) for g=0.5 and g=0.9 ===")
for g in [0.2, 0.5, 0.8, 0.9]:
    mpole = float(mu_pole_exact(g))
    print(f"\ng = {g}, mu_pole = {mpole:.8f}")
    for dmu in [0.005, 0.01, 0.02, 0.05, 0.10, 0.15, 0.20, 0.25]:
        mu = mpole + dmu
        if mu >= 1.0:
            continue
        # Sample t logarithmically and linearly to see if dG > 0 ever happens
        ts = [0.5, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0, 15.0, 20.0, 30.0, 50.0, 100.0]
        max_dG = -mp.mpf("1e10")
        t_at_max = None
        for tv in ts:
            _, dG = G_and_dG_hankel(tv, mu, g)
            if dG > max_dG:
                max_dG = dG
                t_at_max = tv
        print(f"  mu={mu:.6f} (mu_pole+{dmu:.3f}): max sampled dG = {mp.nstr(max_dG, 8)} at t={t_at_max}")
