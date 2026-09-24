#!/usr/bin/env python3
"""
classify_ode.py  --  classify an autonomous first-order ODE   u' = g(u)

(g a rational function with numeric coefficients) following

  P. Kumbhakar, "New and general type meromorphic 1-forms on curves",
  Comm. Algebra 54 (2026), and Noordman-van der Put-Top (2022).

NOTE: this is the lightweight Python fallback. The main program is
classify_ode.sage (SageMath), which works with exact algebraic numbers and also
uses the faster residue criterion described in the README. Use the Sage
version for definitive results.

The associated pair is (P^1, omega) with omega = dx / g(x).

Output
  * type: exact / exponential / general   (Weierstrass is impossible on P^1:
    a Weierstrass-type form is holomorphic, and P^1 has no nonzero
    holomorphic 1-forms)
  * new / old.  If old, an explicit phi and eta with phi^* eta = omega.

Method for new/old (general type)
  If omega = phi^* eta with deg(phi) = d >= 2, then eta is general type, so it
  has a zero Q1 and a pole Q2.  After a Moebius map, Q1 = 0 and Q2 = oo, so
      phi = prod_{P in A} (x-P)^{e_P} / prod_{S in B} (x-S)^{e_S},
  where A is a set of zeros of omega and B is a set of poles of omega.
  Lemma 3.1  e_P (ord_Q eta + 1) = ord_P omega + 1  fixes the exponents,
  and at simple poles Lemma 3.2(v) fixes them through residue ratios.
  That leaves finitely many candidates.  A candidate works iff C(phi) is a
  differential subfield, i.e.  delta(phi) = g * phi'  lies in C(phi).
  The check is done at 60-digit precision and then confirmed symbolically
  whenever the zeros and poles are expressible in radicals.

Usage
  python classify_ode.py "y^2*(y-1)^3*(y-2)^5"
  python classify_ode.py "u' = u/(u+1)"
  python classify_ode.py            (interactive)
"""
import sys
import random
import itertools
from collections import Counter
from fractions import Fraction

import sympy as sp
import mpmath as mp

mp.mp.dps = 60
ZERO_TOL = mp.mpf(10) ** -30
x = sp.Symbol('x')
y = sp.Symbol('y')
INF = 'oo'


# --------------------------------------------------------------------------
# parsing
# --------------------------------------------------------------------------
def parse_rhs(s):
    s = s.strip().replace('^', '**')
    if '=' in s:
        s = s.split('=', 1)[1]
    loc = {c: sp.Symbol(c) for c in 'uyxzwtv'}
    loc.update({'I': sp.I, 'sqrt': sp.sqrt, 'pi': sp.pi, 'E': sp.E})
    expr = sp.sympify(s, locals=loc)
    syms = expr.free_symbols
    if len(syms) > 1:
        raise ValueError("only one variable is allowed - give parameters "
                         "numeric values (found %s)" % sorted(map(str, syms)))
    if syms:
        expr = expr.subs(syms.pop(), x)
    g = sp.cancel(sp.together(expr))
    if g == 0:
        raise ValueError("g = 0 is not a valid equation")
    return g


# --------------------------------------------------------------------------
# zeros / poles / residues of omega = dx/g
# --------------------------------------------------------------------------
def to_mpc(v):
    v = sp.N(v, 70)
    re_, im_ = sp.re(v), sp.im(v)
    return mp.mpc(mp.mpf(str(re_)), mp.mpf(str(im_)))


def roots_with_mult(expr):
    out = []
    if sp.Poly(expr, x).degree() <= 0:
        return out
    for f, m in sp.factor_list(expr, x)[1]:
        fp = sp.Poly(f, x)
        if fp.degree() <= 0:
            continue
        r = sp.roots(fp, cubics=False, quartics=False)
        if sum(r.values()) < fp.degree():
            r = Counter(fp.all_roots())          # exact CRootOf objects
        for rt, mm in r.items():
            out.append((rt, mm * m))
    return out


class Pt:
    def __init__(self, pt, order):
        self.pt = pt                          # sympy number or INF
        self.num = None if pt == INF else to_mpc(pt)
        self.order = order                    # ord of omega here
        self.res = mp.mpc(0)

    @property
    def w(self):
        return -self.order

    def label(self):
        if self.pt == INF:
            return 'oo'
        return str(self.pt) if not self.pt.has(sp.CRootOf) \
            else mp.nstr(self.num, 12)


def poly_coeffs_num(expr):
    """low -> high numeric coefficients"""
    c = sp.Poly(expr, x).all_coeffs()[::-1]
    return [to_mpc(ci) for ci in c]


def series_mul(a, b, L):
    out = [mp.mpc(0)] * L
    for i, ai in enumerate(a[:L]):
        if ai == 0:
            continue
        for j, bj in enumerate(b[:L - i]):
            out[i + j] += ai * bj
    return out


def residue_at(a, w, qc, plead, other_roots):
    """residue at finite pole a of order w of q(x) / (plead * prod (x-b)^m)"""
    L = w
    ser = [mp.mpc(0)] * L                       # q(a+s)
    for i, c in enumerate(qc):
        if c == 0:
            continue
        for j in range(min(i, L - 1) + 1):
            ser[j] += c * mp.binomial(i, j) * a ** (i - j)
    for b, m in other_roots:
        u = a - b
        inv = [(-1) ** j * mp.binomial(m + j - 1, j) * u ** (-m - j)
               for j in range(L)]
        ser = series_mul(ser, inv, L)
    return ser[L - 1] / plead


def analyse(g):
    p, q = sp.fraction(sp.cancel(g))            # g = p/q,  omega = q/p dx
    P, Q = sp.Poly(p, x), sp.Poly(q, x)
    zeros, poles = [], []
    for rt, m in roots_with_mult(q):
        zeros.append(Pt(rt, m))
    proots = roots_with_mult(p)
    for rt, m in proots:
        poles.append(Pt(rt, -m))
    oinf = P.degree() - Q.degree() - 2
    # residues at finite poles
    qc = poly_coeffs_num(q)
    plead = to_mpc(P.LC())
    numroots = [(to_mpc(r), m) for r, m in proots]
    for k, S in enumerate(poles):
        others = [numroots[j] for j in range(len(numroots)) if j != k]
        S.res = residue_at(S.num, S.w, qc, plead, others)
    if oinf != 0:
        pinf = Pt(INF, oinf)
        if oinf > 0:
            zeros.append(pinf)
        else:
            pinf.res = -sum((S.res for S in poles), mp.mpc(0))
            poles.append(pinf)
    return zeros, poles


def is_zero(z):
    return abs(z) < ZERO_TOL


def rational_ratio(a, b):
    """a/b if it is (numerically) a rational number, else None"""
    r = a / b
    if abs(r.imag) > ZERO_TOL * (1 + abs(r)):
        return None
    fr = Fraction(mp.nstr(r.real, 55)).limit_denominator(10 ** 9)
    if abs(mp.mpf(fr.numerator) / fr.denominator - r.real) < ZERO_TOL * (1 + abs(r)):
        return fr
    return None


def nice(z):
    """pretty-print a numeric residue"""
    if is_zero(z):
        return '0'
    try:
        v = sp.nsimplify(complex(z), rational=False, tolerance=1e-25)
        if abs(complex(sp.N(v, 40)) - complex(z)) < 1e-25:
            return str(v)
    except Exception:
        pass
    return mp.nstr(z, 15)


# --------------------------------------------------------------------------
# type (Corollary 3.4 / Proposition 3.3)
# --------------------------------------------------------------------------
def classify_type(zeros, poles):
    if all(is_zero(S.res) for S in poles):
        return 'exact'
    if all(S.w == 1 for S in poles):
        r0 = poles[0].res
        if all(rational_ratio(S.res, r0) is not None for S in poles):
            return 'exponential'
    return 'general'


# --------------------------------------------------------------------------
# new / old for general type
# --------------------------------------------------------------------------
def subsets_exact_sum(items, target):
    """items: list of (obj, weight>0); yield lists with total weight == target"""
    def rec(i, remaining, chosen):
        if remaining == 0:
            yield list(chosen)
            return
        if i == len(items):
            return
        obj, wgt = items[i]
        if wgt <= remaining:
            chosen.append((obj, wgt))
            yield from rec(i + 1, remaining - wgt, chosen)
            chosen.pop()
        yield from rec(i + 1, remaining, chosen)
    yield from rec(0, target, [])


def pole_fibres(poles, dmax):
    """possible fibres B over a pole of eta, all containing a fixed pole S0"""
    high = [S for S in poles if S.w >= 2]
    simple = [S for S in poles if S.w == 1]
    out = []
    if high:
        S0 = high[0]
        for m in range(2, S0.w + 1):                 # order of eta's pole
            if (S0.w - 1) % (m - 1):
                continue
            e0 = (S0.w - 1) // (m - 1)
            others = [(S, (S.w - 1) // (m - 1)) for S in high
                      if S is not S0 and (S.w - 1) % (m - 1) == 0]
            for d in range(max(2, e0), dmax + 1):
                for sub in subsets_exact_sum(others, d - e0):
                    out.append((d, [(S0, e0)] + sub))
    else:
        S0 = simple[0]
        others = []
        for S in simple:
            if S is S0:
                continue
            q = rational_ratio(S.res, S0.res)
            if q is not None and q > 0:
                others.append((S, q))
        for size in range(0, min(len(others), dmax - 1) + 1):
            for T in itertools.combinations(others, size):
                s = 1 + sum(q for _, q in T)
                for d in range(2, dmax + 1):
                    e0 = Fraction(d) / s
                    es = [e0] + [e0 * q for _, q in T]
                    if all(e.denominator == 1 for e in es):
                        out.append((d, [(S0, int(e0))] +
                                    [(S, int(e0 * q)) for S, q in T]))
    return out


def zero_fibres(zeros, d):
    """possible fibres A over a zero of eta of order k-1 >= 1, total degree d"""
    kmax = max(Z.order + 1 for Z in zeros)
    for k in range(2, kmax + 1):
        items = [(Z, (Z.order + 1) // k) for Z in zeros if (Z.order + 1) % k == 0]
        for A in subsets_exact_sum(items, d):
            yield A


def poly_from_roots(rs):
    """high -> low coefficients of prod (t - r)^m"""
    c = [mp.mpc(1)]
    for r, m in rs:
        for _ in range(m):
            new = c + [mp.mpc(0)]
            for i in range(len(c)):
                new[i + 1] -= r * c[i]
            c = new
    return c


def numeric_subfield_test(A, B, d, gnum, trials=3):
    Af = [(Z.num, e) for Z, e in A if Z.pt != INF]
    Bf = [(S.num, e) for S, e in B if S.pt != INF]

    def phi(t):
        v = mp.mpc(1)
        for a, e in Af:
            v *= (t - a) ** e
        for b, e in Bf:
            v /= (t - b) ** e
        return v

    def h(t):  # delta(phi) = g * phi'
        L = sum(e / (t - a) for a, e in Af) - sum(e / (t - b) for b, e in Bf)
        return gnum(t) * phi(t) * L

    N, D = poly_from_roots(Af), poly_from_roots(Bf)
    n = max(len(N), len(D))
    N = [mp.mpc(0)] * (n - len(N)) + N
    D = [mp.mpc(0)] * (n - len(D)) + D
    rng = random.Random(12345)
    for _ in range(trials):
        x0 = mp.mpc(rng.uniform(-2, 2), rng.uniform(-2, 2))
        y0, target = phi(x0), h(x0)
        poly = [N[i] - y0 * D[i] for i in range(n)]
        while poly and abs(poly[0]) < ZERO_TOL:
            poly.pop(0)
        if len(poly) - 1 != d:
            return False
        try:
            ts = mp.polyroots(poly, maxsteps=800, extraprec=400)
        except mp.libmp.NoConvergence:
            return False
        for t in ts:
            if abs(h(t) - target) > mp.mpf(10) ** -20 * (1 + abs(target)):
                return False
    return True


def exact_eta(A, B, d, g):
    """Return (phi, eta_coefficient) with phi^*(eta_coefficient dy) = dx/g,
    exactly, or None if the points are not expressible in radicals."""
    pts = [Z.pt for Z, _ in A + B if Z.pt != INF]
    if any(p.has(sp.CRootOf) for p in pts):
        return None
    phi = sp.Integer(1)
    for Z, e in A:
        if Z.pt != INF:
            phi *= (x - Z.pt) ** e
    for S, e in B:
        if S.pt != INF:
            phi /= (x - S.pt) ** e
    phi = sp.cancel(sp.expand(phi))
    h = sp.cancel(g * sp.diff(phi, x))
    hn, hd = sp.fraction(h)
    deg = max(sp.Poly(hn, x).degree(), sp.Poly(hd, x).degree())
    if deg % d:
        return None
    k = deg // d
    N, D = sp.fraction(phi)
    a = sp.symbols('a0:%d' % (k + 1))
    b = sp.symbols('b0:%d' % (k + 1))
    basis = [sp.expand(N ** i * D ** (k - i)) for i in range(k + 1)]
    expr = sp.expand(hn * sum(bi * Bi for bi, Bi in zip(b, basis))
                     - hd * sum(ai * Bi for ai, Bi in zip(a, basis)))
    eqs = sp.Poly(expr, x).coeffs()
    M, _ = sp.linear_eq_to_matrix(eqs, list(a) + list(b))
    ns = M.nullspace(simplify=True)
    if not ns:
        return None
    v = ns[0]
    Ay = sum(v[i] * y ** i for i in range(k + 1))
    By = sum(v[k + 1 + i] * y ** i for i in range(k + 1))
    eta = sp.factor(sp.cancel(By / Ay))          # eta = eta(y) dy,  R = A/B
    check = sp.simplify(sp.cancel(eta.subs(y, phi) * sp.diff(phi, x) - 1 / g))
    if check != 0:
        return None
    return phi, eta


def find_pullback(zeros, poles, g):
    dmax = sum(Z.order + 1 for Z in zeros) // 2       # Proposition 3.6
    if dmax < 2:
        return None
    gnum = sp.lambdify(x, g, 'mpmath')
    tested = set()
    for d, B in pole_fibres(poles, dmax):
        for A in zero_fibres(zeros, d):
            key = (tuple((id(Z), e) for Z, e in A), tuple((id(S), e) for S, e in B))
            if key in tested:
                continue
            tested.add(key)
            if numeric_subfield_test(A, B, d, gnum):
                return d, A, B
    return None


def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, int(n ** 0.5) + 1))


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------
def classify(rhs, verbose=True):
    g = parse_rhs(rhs) if isinstance(rhs, str) else sp.cancel(rhs)
    zeros, poles = analyse(g)
    out = {'g': g, 'zeros': zeros, 'poles': poles}
    lines = ["Equation   u' = %s" % sp.factor(g).subs(x, sp.Symbol('u')),
             "1-form     omega = dx / (%s)" % sp.factor(g)]
    div = ' '.join('%+d[%s]' % (Z.order, Z.label()) for Z in zeros + poles)
    lines.append("div(omega) = " + div)
    for S in poles:
        lines.append("   residue at %-12s (pole of order %d): %s"
                     % (S.label(), S.w, nice(S.res)))

    typ = classify_type(zeros, poles)
    out['type'] = typ
    lines.append("TYPE: %s type   (not Weierstrass: impossible on P^1)" % typ)

    if typ == 'exact':
        new = len(poles) == 1 and poles[0].w == 2
        lines.append("NEW/OLD: %s   (exact type is new iff div(omega) = -2P, "
                     "Cor. 3.4)" % ('NEW' if new else 'OLD'))
        if not new:
            H = sp.integrate(1 / g, x)
            lines.append("   omega = d(h) with h = %s of degree >= 2, i.e. a "
                         "pullback of (P^1, dy) by h" % sp.simplify(H))
        out['new'] = new
    elif typ == 'exponential':
        lines.append("NEW/OLD: OLD   (exponential type is always old)")
        out['new'] = False
    else:
        cert = None
        if len(zeros) == 1 and is_prime(zeros[0].order + 1):
            cert = "Proposition 5.4 (single zero of order m with m+1 prime)"
        nz = [S.res for S in poles if not is_zero(S.res)]
        if cert is None and len(nz) >= 2 and all(
                rational_ratio(r1, r2) is None
                for r1, r2 in itertools.combinations(nz, 2)):
            cert = "Theorem 1.2 with g=0 (no two nonzero residues Q-dependent)"
        if cert:
            lines.append("NEW/OLD: NEW   [certificate: %s]" % cert)
            out['new'] = True
        else:
            res = find_pullback(zeros, poles, g)
            if res is None:
                lines.append("NEW/OLD: NEW   (no candidate phi of degree "
                             ">= 2 makes C(phi) a differential subfield)")
                out['new'] = True
            else:
                d, A, B = res
                out['new'] = False
                lines.append("NEW/OLD: OLD   (proper pullback of degree %d found)" % d)
                lines.append("   phi = prod (x-P)^e / prod (x-S)^e  with")
                lines.append("     zeros of phi: " + ', '.join(
                    '%s^%d' % (Z.label(), e) for Z, e in A))
                lines.append("     poles of phi: " + ', '.join(
                    '%s^%d' % (S.label(), e) for S, e in B))
                ex = exact_eta(A, B, d, g)
                if ex:
                    phi, eta = ex
                    out['phi'], out['eta'] = phi, eta
                    lines.append("   phi(x) = %s" % sp.factor(phi))
                    lines.append("   eta    = (%s) dy" % eta)
                    lines.append("   i.e. u' = g(u) comes from  v' = %s  "
                                 "via v = phi(u)  (verified exactly)"
                                 % sp.factor(1 / eta))
                    lines.append("   (run the script on that equation to see "
                                 "whether it is itself new)")
                else:
                    lines.append("   (verified at 60 digits; points are not in "
                                 "radicals, so eta is not printed exactly)")
    if verbose:
        print('\n'.join(lines))
        print()
    return out


if __name__ == '__main__':
    if len(sys.argv) > 1:
        for arg in sys.argv[1:]:
            classify(arg)
    else:
        print("Enter g(u) for u' = g(u)  (e.g.  u^3-u^2  or  u/(u+1)),"
              " empty line to quit.")
        while True:
            try:
                s = input('> ').strip()
            except EOFError:
                break
            if not s:
                break
            try:
                classify(s)
            except Exception as err:
                print('error:', err, '\n')
