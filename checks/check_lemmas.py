#!/usr/bin/env python3
"""Independent numerical checks for the note "The N^(sqrt2) Hurwitz construction, written out".

Implements Appendix B of "A 2^o(n) time algorithm for 3-SAT" (Claude/Anthropic, 26 Oct 2026)
from its definitions, in exact rational arithmetic, and checks:

  1. the Heisenberg relation  nabla_k nabla_{-l} - nabla_{-l} nabla_k = k [k=l] Id;
  2. Lemma 10:  a^mu[-h] b^nu = h! [mu = nu]  for all partitions mu, nu of h;
  3. Lemma 9 (a), (b), (c) with a = a^mu (inhomogeneous) and b = b^nu, on every basis monomial
     of V_E, E <= EMAX;
  4. the crossing identity  sum_s A_s = h! [xi = nu][eta = ups],  indices = all partitions of h;
  5. the two factorizations (54) and (55) of every A_s, term by term;
  6. the explicit bilinear identity  h! (sum X^2)(sum Y^2) = sum_k f_k g_k,  multiplied out as a
     polynomial in 2 p(h) commuting variables, with the cheaper factorization for each s;
  7. the product count  sum_s min(R_row, R_col) = sum_j (4h - 2j + 1) p(j), and its exponent.

Written from the paper's text, not from any other implementation. Python 3, standard library only.
Run:  python3 -I check_lemmas.py [--hmax 5] [--emax 4] [--hbil 5]
"""
import argparse
import itertools
import math
import sys
import time
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache

# ---------------------------------------------------------------- partitions, binomials

@lru_cache(maxsize=None)
def partitions(n, maxpart=None):
    """Partitions of n as nonincreasing tuples."""
    if maxpart is None:
        maxpart = n
    if n == 0:
        return ((),)
    out = []
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            out.append((k,) + rest)
    return tuple(out)


def p(n):
    return len(partitions(n)) if n >= 0 else 0


def binom(k, j):
    """C(k, j) = k(k-1)...(k-j+1)/j! for integer k and j >= 0; 0 for j < 0."""
    if j < 0:
        return 0
    num = 1
    for t in range(j):
        num *= (k - t)
    return num // math.factorial(j)


def mult(mu, k):
    return sum(1 for x in mu if x == k)


def z(mu):
    out = 1
    for k in set(mu):
        m = mult(mu, k)
        out *= k ** m * math.factorial(m)
    return out


def norm(parts):
    return tuple(sorted(parts, reverse=True))

# ---------------------------------------------------------------- the ring V = Q[t1, t2, ...]
# A polynomial is a dict {partition (nonincreasing tuple): coefficient}; t^mu <-> mu.

def padd(f, g, c=1):
    out = dict(f)
    for m, v in g.items():
        out[m] = out.get(m, 0) + c * v
        if out[m] == 0:
            del out[m]
    return out


def nabla(k, f):
    """nabla_{-l} = multiplication by t_l (k = -l < 0); nabla_k = k d/dt_k (k > 0)."""
    out = {}
    if k < 0:
        l = -k
        for m, v in f.items():
            mm = norm(m + (l,))
            out[mm] = out.get(mm, 0) + v
    elif k > 0:
        for m, v in f.items():
            c = mult(m, k)
            if c:
                lst = list(m)
                lst.remove(k)
                mm = tuple(lst)
                out[mm] = out.get(mm, 0) + v * k * c
    return {m: v for m, v in out.items() if v != 0}


def weight(mu):
    return sum(mu)


def compositions(total, n):
    """Ordered n-tuples of positive integers with the given sum."""
    if n == 0:
        if total == 0:
            yield ()
        return
    for first in range(1, total - n + 2):
        for rest in compositions(total - first, n - 1):
            yield (first,) + rest


@lru_cache(maxsize=None)
def op_mon_on_mon(mu, r, sigma):
    """(t^mu)[r] t^sigma, from display (47): sum over nonzero k_i (one per listed part mu_i) with
    sum k_i = -r of  prod C(-k_i-1, mu_i-1) * prod_{k_i<0} nabla_{k_i} * prod_{k_i>0} nabla_{k_i},
    differentiations applied first. Returned as a frozen tuple of (monomial, coeff)."""
    n = len(mu)
    E = weight(sigma)
    out = {}
    f0 = {sigma: 1}
    for signs in itertools.product((1, -1), repeat=n):
        pos = [i for i in range(n) if signs[i] == 1]
        neg = [i for i in range(n) if signs[i] == -1]
        # positive k's: total P <= E (else the differentiations kill t^sigma)
        for P in range(len(pos), E + 1):
            L = r + P            # sum of l_i over negative positions (k_i = -l_i): -sum k = r
            if neg:
                if L < len(neg):
                    continue
            else:
                if L != 0:
                    continue
            for kpos in compositions(P, len(pos)):
                f = f0
                for kk in kpos:
                    f = nabla(kk, f)
                    if not f:
                        break
                if not f:
                    continue
                for lneg in compositions(L, len(neg)):
                    coef = 1
                    for idx, kk in zip(pos, kpos):
                        coef *= binom(-kk - 1, mu[idx] - 1)
                    for idx, ll in zip(neg, lneg):
                        coef *= binom(ll - 1, mu[idx] - 1)
                    if coef == 0:
                        continue
                    g = f
                    for ll in lneg:
                        g = nabla(-ll, g)
                    for m, v in g.items():
                        out[m] = out.get(m, 0) + coef * v
    return tuple((m, v) for m, v in out.items() if v != 0)


def op(a, r, f):
    """a[r] f for polynomials a, f (linear in both)."""
    out = {}
    for am, av in a.items():
        for fm, fv in f.items():
            for m, v in op_mon_on_mon(am, r, fm):
                out[m] = out.get(m, 0) + av * fv * v
    return {m: v for m, v in out.items() if v != 0}


def pmul(f, g):
    out = {}
    for m1, v1 in f.items():
        for m2, v2 in g.items():
            m = norm(m1 + m2)
            out[m] = out.get(m, 0) + v1 * v2
    return {m: v for m, v in out.items() if v != 0}


def y_poly(n):
    return {(j,): binom(n, j) for j in range(1, n + 1)}


def a_fam(mu):
    a = {(): 1}
    for n in mu:
        a = pmul(a, {m: (-1) ** (n - 1) * v for m, v in y_poly(n).items()})
    return a


def b_fam(mu):
    h = weight(mu)
    assert math.factorial(h) % z(mu) == 0
    return {mu: math.factorial(h) // z(mu)}


def angle(a, i, h):
    """a<i> = sum_{h'} C(h'+h, i) * (weight-h' part of a)."""
    return {m: v * binom(weight(m) + h, i) for m, v in a.items() if binom(weight(m) + h, i) != 0}


def Q(h, s, a, b, f, exchanged=False):
    """Display (48): Q_s(a,b) f = sum_{i=0}^{2h} (-1)^i a<i>[s-h+i] b[h-s-i] f (exchanged: b acts last)."""
    out = {}
    for i in range(0, 2 * h + 1):
        ai = angle(a, i, h)
        if not ai:
            continue
        if not exchanged:
            g = op(ai, s - h + i, op(b, h - s - i, f))
        else:
            g = op(b, h - s - i, op(ai, s - h + i, f))
        out = padd(out, g, (-1) ** i)
    return out

# ---------------------------------------------------------------- checks

results = []


def report(name, ok, detail=""):
    results.append((name, ok))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""), flush=True)


def check_heisenberg(K=4, E=4):
    ok = True
    for k in range(1, K + 1):
        for l in range(1, K + 1):
            for e in range(E + 1):
                for sig in partitions(e):
                    f = {sig: 1}
                    lhs = padd(nabla(k, nabla(-l, f)), nabla(-l, nabla(k, f)), -1)
                    rhs = {sig: k} if k == l else {}
                    ok &= (lhs == rhs)
    report("Heisenberg relation nabla_k nabla_{-l} - nabla_{-l} nabla_k = k[k=l]", ok, f"k,l<={K}, E<={E}")


def check_lemma10(hmax):
    for h in range(1, hmax + 1):
        ok = True
        hf = math.factorial(h)
        for mu in partitions(h):
            a = a_fam(mu)
            assert all(weight(m) <= h for m in a)
            for nu in partitions(h):
                val = op(a, -h, b_fam(nu))
                want = {(): hf} if mu == nu else {}
                ok &= (val == want)
        report(f"Lemma 10, h={h}: a^mu[-h] b^nu = h![mu=nu] for all {p(h)}^2 pairs", ok)


def check_lemma9(hmax, emax):
    for h in range(1, hmax + 1):
        ok_a = ok_b = ok_c = True
        n = 0
        for mu in partitions(h):
            a = a_fam(mu)
            for nu in partitions(h):
                b = b_fam(nu)
                pair = op(a, -h, b).get((), 0)
                for E in range(0, emax + 1):
                    for sig in partitions(E):
                        f = {sig: 1}
                        total = {}
                        # |s| <= 2(E+h)+2: beyond E+h the vanishing is trivial only for Q_s with s > E+h;
                        # for s < -(E+h), and for Q'_s with s > E+h, it is a real cancellation.
                        for s in range(-2 * (E + h) - 2, 2 * (E + h) + 3):
                            q = Q(h, s, a, b, f)
                            q2 = Q(h, s, a, b, f, exchanged=True)
                            ok_a &= (q == q2)
                            if abs(s) > E + h:
                                ok_b &= (q == {})
                            else:
                                total = padd(total, q)
                        ok_c &= (total == ({sig: pair} if pair else {}))
                        n += 1
        report(f"Lemma 9(a), h={h}: Q_s equals Q_s with the factors exchanged (Q_s = Q'_s)", ok_a, f"{n} (mu,nu,t^sigma) cases, |sigma|<={emax}, |s|<=2(E+h)+2")
        report(f"Lemma 9(b), h={h}: Q_s = 0 on V_E for E+h < |s| <= 2(E+h)+2", ok_b)
        report(f"Lemma 9(c), h={h}: sum_s Q_s = (a[-h]b) Id on V_E", ok_c)


def pieces(h):
    """A[s][(xi, eta, ups, nu)] = [t^ups] Q_s(a^xi, b^nu) t^eta, all partitions of h."""
    P = partitions(h)
    A = {}
    for s in range(-2 * h, 2 * h + 1):
        As = {}
        for xi in P:
            a = a_fam(xi)
            for nu in P:
                b = b_fam(nu)
                for eta in P:
                    q = Q(h, s, a, b, {eta: 1})
                    for ups in P:
                        c = q.get(ups, 0)
                        if c:
                            As[(xi, eta, ups, nu)] = c
        A[s] = As
    return A


def check_crossing(hmax):
    for h in range(1, hmax + 1):
        t0 = time.time()
        P = partitions(h)
        A = pieces(h)
        hf = math.factorial(h)
        ok = True
        for xi, eta, ups, nu in itertools.product(P, repeat=4):
            tot = sum(A[s].get((xi, eta, ups, nu), 0) for s in A)
            ok &= (tot == (hf if (xi == nu and eta == ups) else 0))
        report(f"crossing identity, h={h}, N=p(h)={len(P)}: sum_s A_s = h![xi=nu][eta=ups] on all N^4 inputs", ok,
               f"{time.time() - t0:.1f}s")


def row_factors(h, s, i, sigma, xi, eta, nu, ups):
    """Term (i, sigma) of (54): (-1)^i [t^sigma] a<i>[s-h+i] t^eta  *  [t^ups] b[h-s-i] t^sigma."""
    F = (-1) ** i * op(angle(a_fam(xi), i, h), s - h + i, {eta: 1}).get(sigma, 0)
    G = op(b_fam(nu), h - s - i, {sigma: 1}).get(ups, 0)
    return F, G


def col_factors(h, s, i, sigma, xi, eta, nu, ups):
    """Term (i, sigma) of (55): (-1)^i [t^ups] a<i>[s-h+i] t^sigma  *  [t^sigma] b[h-s-i] t^eta."""
    F = (-1) ** i * op(angle(a_fam(xi), i, h), s - h + i, {sigma: 1}).get(ups, 0)
    G = op(b_fam(nu), h - s - i, {eta: 1}).get(sigma, 0)
    return F, G


def Rrow(h, s):
    return sum(p(s + i) for i in range(2 * h + 1))


def Rcol(h, s):
    return sum(p(2 * h - s - i) for i in range(2 * h + 1))


def check_factorizations(hmax):
    for h in range(1, hmax + 1):
        P = partitions(h)
        A = pieces(h)
        ok_row = ok_col = ok_cnt = ok_dir = True
        for s in range(-2 * h, 2 * h + 1):
            rterms = [(i, sg) for i in range(2 * h + 1) for sg in (partitions(s + i) if s + i >= 0 else ())]
            cterms = [(i, sg) for i in range(2 * h + 1) for sg in (partitions(2 * h - s - i) if 2 * h - s - i >= 0 else ())]
            ok_cnt &= (len(rterms) == Rrow(h, s) and len(cterms) == Rcol(h, s))
            ok_dir &= (Rcol(h, s) == Rrow(h, -s))
            ok_dir &= (Rcol(h, s) <= Rrow(h, s)) if s >= 0 else (Rrow(h, s) <= Rcol(h, s))
            for xi, eta, ups, nu in itertools.product(P, repeat=4):
                want = A[s].get((xi, eta, ups, nu), 0)
                r = sum(F * G for F, G in (row_factors(h, s, i, sg, xi, eta, nu, ups) for i, sg in rterms))
                c = sum(F * G for F, G in (col_factors(h, s, i, sg, xi, eta, nu, ups) for i, sg in cterms))
                ok_row &= (r == want)
                ok_col &= (c == want)
        report(f"display (54), row-wise factorization, h={h}: equals A_s for all s and inputs", ok_row)
        report(f"display (55), column-wise factorization, h={h}: equals A_s for all s and inputs", ok_col)
        report(f"term counts, h={h}: |(54)| = R_s^row, |(55)| = R_s^col, R_s^col = R_(-s)^row", ok_cnt and ok_dir)


def check_bilinear(h):
    """Build the bilinear forms with the cheaper factorization for each s and multiply out."""
    t0 = time.time()
    P = partitions(h)
    idx = {mu: n for n, mu in enumerate(P)}
    N = len(P)
    hf = math.factorial(h)
    # monomials in X_0..X_{N-1}, Y_0..Y_{N-1}: (sorted tuple of X indices, sorted tuple of Y indices)
    rhs = defaultdict(int)
    K = nonzero = 0
    for s in range(-2 * h, 2 * h + 1):
        use_row = Rrow(h, s) < Rcol(h, s)       # ties (s = 0) go to columns; either is valid
        if use_row:
            terms = [(i, sg) for i in range(2 * h + 1) for sg in (partitions(s + i) if s + i >= 0 else ())]
        else:
            terms = [(i, sg) for i in range(2 * h + 1) for sg in (partitions(2 * h - s - i) if 2 * h - s - i >= 0 else ())]
        for i, sg in terms:
            K += 1
            f = {}   # bilinear form: {(X index, Y index): coeff}
            g = {}
            if use_row:
                # f = sum_{xi,eta} (-1)^i [t^sigma] a^xi<i>[s-h+i] t^eta  X_xi Y_eta
                # g = sum_{nu,ups} [t^ups] b^nu[h-s-i] t^sigma  X_nu Y_ups
                for xi in P:
                    ai = angle(a_fam(xi), i, h)
                    for eta in P:
                        c = (-1) ** i * op(ai, s - h + i, {eta: 1}).get(sg, 0)
                        if c:
                            f[(idx[xi], idx[eta])] = c
                for nu in P:
                    q = op(b_fam(nu), h - s - i, {sg: 1})
                    for ups in P:
                        c = q.get(ups, 0)
                        if c:
                            g[(idx[nu], idx[ups])] = c
            else:
                # f = sum_{xi,ups} (-1)^i [t^ups] a^xi<i>[s-h+i] t^sigma  X_xi Y_ups
                # g = sum_{nu,eta} [t^sigma] b^nu[h-s-i] t^eta  X_nu Y_eta
                for xi in P:
                    q = op(angle(a_fam(xi), i, h), s - h + i, {sg: 1})
                    for ups in P:
                        c = (-1) ** i * q.get(ups, 0)
                        if c:
                            f[(idx[xi], idx[ups])] = c
                for nu in P:
                    b = b_fam(nu)
                    for eta in P:
                        c = op(b, h - s - i, {eta: 1}).get(sg, 0)
                        if c:
                            g[(idx[nu], idx[eta])] = c
            if f and g:
                nonzero += 1
            for (x1, y1), c1 in f.items():
                for (x2, y2), c2 in g.items():
                    rhs[(tuple(sorted((x1, x2))), tuple(sorted((y1, y2))))] += c1 * c2
    rhs = {m: v for m, v in rhs.items() if v != 0}
    lhs = {((x, x), (y, y)): hf for x in range(N) for y in range(N)}
    ok = (rhs == lhs)
    formula = sum((4 * h - 2 * j + 1) * p(j) for j in range(2 * h + 1))
    report(f"bilinear identity, h={h}: {hf}*(sum_{{i<{N}}} X_i^2)(sum_{{j<{N}}} Y_j^2) = sum_k f_k g_k as polynomials",
           ok, f"K = {K} products ({nonzero} with both forms nonzero), {time.time() - t0:.1f}s")
    report(f"product count, h={h}: K = sum_j (4h-2j+1) p(j) = {formula}", K == formula)


def pentagonal_p(nmax):
    """p(0..nmax) by Euler's pentagonal recurrence (exact integers)."""
    P = [0] * (nmax + 1)
    P[0] = 1
    for n in range(1, nmax + 1):
        tot = 0
        k = 1
        while True:
            g1 = k * (3 * k - 1) // 2
            if g1 > n:
                break
            sgn = 1 if k % 2 else -1
            tot += sgn * P[n - g1]
            g2 = k * (3 * k + 1) // 2
            if g2 <= n:
                tot += sgn * P[n - g2]
            k += 1
        P[n] = tot
    return P


def exponent_table(lams):
    H = lambda x: -x * math.log2(x) - (1 - x) * math.log2(1 - x)
    lo, hi = 1e-9, 0.5
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if H(mid) < 0.5 else (lo, mid)
    hru = 1 + 2 * H(lo / 2)
    print(f"\nexponent of the product count K(lambda) = sum_j (4h-2j+1) p(j), h least with p(h) >= 2^lambda")
    print(f"(Hrubes 2024 exponent for comparison: 1 + 2H(alpha/2) with H(alpha) = 1/2, = {hru:.4f})")
    Pt = pentagonal_p(2 * 28000)
    print(f"{'lambda':>7} {'h':>7} {'log2 K':>10} {'log2K/lambda':>13}")

    def hK(lam):
        h = 2
        while Pt[h] < 2 ** lam:
            h += 1
        return h, sum((4 * h - 2 * j + 1) * Pt[j] for j in range(2 * h + 1))

    cross = None
    for lam in range(40, 120):
        h, K = hK(lam)
        if math.log2(K) / lam < hru:
            cross = lam
            break
    rows = []
    for lam in lams:
        h, K = hK(lam)
        rows.append((lam, h, math.log2(K), math.log2(K) / lam))
    for lam, h, lk, e in rows:
        print(f"{lam:>7} {h:>7} {lk:>10.1f} {e:>13.4f}")
    print(f"first lambda with exponent below {hru:.4f}: {cross}  (sqrt 2 = {math.sqrt(2):.4f})")
    report("exponent table computed", cross is not None)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hmax", type=int, default=5, help="largest h for Lemma 10, crossing, factorizations")
    ap.add_argument("--h9", type=int, default=4, help="largest h for Lemma 9")
    ap.add_argument("--emax", type=int, default=4, help="largest weight E for Lemma 9")
    ap.add_argument("--hbil", type=int, default=5, help="h for the explicit bilinear identity")
    ap.add_argument("--hfac", type=int, default=4, help="largest h for the term-by-term factorization check")
    args = ap.parse_args()
    t0 = time.time()
    check_heisenberg()
    check_lemma10(args.hmax)
    check_lemma9(args.h9, args.emax)
    check_crossing(args.hmax)
    check_factorizations(args.hfac)
    for h in range(2, args.hbil + 1):
        check_bilinear(h)
    exponent_table([10, 20, 40, 60, 70, 80, 100, 200, 400, 600])
    bad = [n for n, ok in results if not ok]
    print(f"\n{len(results) - len(bad)}/{len(results)} checks passed in {time.time() - t0:.0f}s")
    print("ALL CHECKS PASSED" if not bad else "FAILURES: " + "; ".join(bad))
    sys.exit(0 if not bad else 1)


if __name__ == "__main__":
    main()
