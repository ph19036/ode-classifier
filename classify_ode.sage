r"""
classify_ode.sage -- classify an autonomous first-order ODE   u' = g(u)

g is a rational function with algebraic coefficients (rationals, I, sqrt(2), ...).
The associated pair is (P^1, omega) with omega = dx/g(x).  The program decides

  * the type: exact / exponential / general
    (Weierstrass type is impossible on P^1: such a form would be holomorphic);
  * new / old, and when old it returns phi, eta with phi^* eta = omega.

Reference: P. Kumbhakar, "New and general type meromorphic 1-forms on curves",
Comm. Algebra 54 (2026) 1918-1935, doi:10.1080/00927872.2025.2569453,
building on Noordman-van der Put-Top, Trans. AMS 375 (2022).

Method for new/old.  If omega = phi^* eta with deg(phi) = d >= 2, then eta is
general type (Prop. 3.5), so it has a zero Q1 and a pole Q2.  After a Moebius
change of the target, Q1 = 0 and Q2 = oo, hence

      phi = prod_{P in A} (x-P)^{e_P} / prod_{S in B} (x-S)^{e_S},

A a set of zeros of omega and B a set of poles of omega (Lemma 3.2).  Lemma 3.1,
e_P (ord eta + 1) = ord_P omega + 1, fixes the exponents; at simple poles
Lemma 3.2(v) fixes them through residue ratios.  B may be taken to contain any
fixed pole S0 of omega.  This leaves finitely many candidates, and a candidate
works iff C(phi) is a differential subfield:  delta(phi) = g * phi'  in C(phi).
Each candidate is screened numerically and then decided by exact linear algebra
over QQbar, so the final answer is exact.

Usage (Sage):
    load("classify_ode.sage")
    classify("u^2*(u-1)^3*(u-2)^5")
    classify("u' = u/(u+1)")
    classify("(u^5 - u^3)/2")
From a terminal:
    sage classify_ode.sage "u^3 - u^2" "u/(u+1)"
"""
import itertools
import re

R = PolynomialRing(QQbar, 'x')
x = R.gen()
K = R.fraction_field()
Ry = PolynomialRing(QQbar, 'y')
yv = Ry.gen()
INF = 'oo'
CF = ComplexField(212)


# --------------------------------------------------------------------------
# input
# --------------------------------------------------------------------------
def parse_rhs(s):
    """string -> g in K = QQbar(x).  Use one variable (u, y, x, ...);
    I, sqrt(...) and rational numbers are allowed as coefficients."""
    if not isinstance(s, str):
        return K(s)
    s = s.strip()
    if '=' in s:
        s = s.split('=', 1)[1]
    X = K.gen()
    loc = {v: X for v in ('u', 'y', 'x', 'z', 'w', 't', 'v')}
    loc.update({'I': QQbar(I), 'i': QQbar(I),
                'sqrt': lambda a: QQbar(a).sqrt()})
    try:
        g = K(sage_eval(s, locals=loc))
    except NameError as err:
        raise ValueError("only one variable (u, y, x, ...) is allowed and "
                         "parameters must be numbers: %s" % err)
    used = [v for v in ('u', 'y', 'x', 'z', 'w', 't', 'v')
            if re.search(r'(?<![A-Za-z_])%s(?![A-Za-z_(])' % v, s)]
    if len(used) > 1:
        raise ValueError("use a single variable, found %s" % used)
    if g == 0:
        raise ValueError("g = 0 is not a valid equation")
    return g


# --------------------------------------------------------------------------
# pretty printing
# --------------------------------------------------------------------------
def pnum(c):
    c = QQbar(c)
    if c in QQ:
        return QQ(c)
    try:
        return c.radical_expression()
    except Exception:
        return c


def pexpr(f, var='x'):
    """element of K or Ry-fraction -> readable symbolic expression"""
    v = SR.var(var)
    num, den = f.numerator(), f.denominator()
    conv = lambda P: sum(pnum(c) * v**i for i, c in enumerate(P.list()))
    return (conv(num) / conv(den)).factor()


class Pt:
    def __init__(self, pt, order):
        self.pt, self.order = pt, order     # pt in QQbar or INF
        self.res = QQbar(0)

    @property
    def w(self):
        return -self.order

    def label(self):
        return 'oo' if self.pt == INF else str(pnum(self.pt))


# --------------------------------------------------------------------------
# zeros, poles and residues of omega = q/p dx   (g = p/q)
# --------------------------------------------------------------------------
def analyse(g):
    p, q = g.numerator(), g.denominator()
    zeros = [Pt(a, m) for a, m in q.roots(QQbar)]
    poles = [Pt(a, -m) for a, m in p.roots(QQbar)]
    for S in poles:
        w = S.w
        p1 = p // (x - S.pt)**w
        PS = PowerSeriesRing(QQbar, 's', default_prec=w)
        s = PS.gen()
        ser = PS(q(x + S.pt).list()) / PS(p1(x + S.pt).list())
        S.res = ser[w - 1]
    oinf = p.degree() - q.degree() - 2
    if oinf != 0:
        P = Pt(INF, oinf)
        if oinf > 0:
            zeros.append(P)
        else:
            P.res = -sum((S.res for S in poles), QQbar(0))
            poles.append(P)
    return zeros, poles


def ratio_in_QQ(a, b):
    r = a / b
    return QQ(r) if r in QQ else None


def classify_type(zeros, poles):
    if all(S.res == 0 for S in poles):
        return 'exact'
    if all(S.w == 1 for S in poles):
        r0 = poles[0].res
        if all(ratio_in_QQ(S.res, r0) is not None for S in poles):
            return 'exponential'
    return 'general'


# --------------------------------------------------------------------------
# candidate fibres
# --------------------------------------------------------------------------
def subsets_exact_sum(items, target):
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
    high = [S for S in poles if S.w >= 2]
    simple = [S for S in poles if S.w == 1]
    out = []
    if high:
        S0 = high[0]
        for m in range(2, S0.w + 1):              # order of the pole of eta
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
            if S is not S0:
                r = ratio_in_QQ(S.res, S0.res)
                if r is not None and r > 0:
                    others.append((S, r))
        for size in range(0, min(len(others), dmax - 1) + 1):
            for T in itertools.combinations(others, size):
                tot = 1 + sum(r for _, r in T)
                for d in range(2, dmax + 1):
                    e0 = QQ(d) / tot
                    es = [e0] + [e0 * r for _, r in T]
                    if all(e in ZZ for e in es):
                        out.append((d, [(S0, ZZ(e0))] +
                                    [(S, ZZ(e0 * r)) for S, r in T]))
    return out


def zero_fibres(zeros, d):
    kmax = max(Z.order + 1 for Z in zeros)
    for k in range(2, kmax + 1):              # k = ord of eta at Q1, plus 1
        items = [(Z, (Z.order + 1) // k) for Z in zeros if (Z.order + 1) % k == 0]
        for A in subsets_exact_sum(items, d):
            yield A


# --------------------------------------------------------------------------
# is C(phi) a differential subfield?
# --------------------------------------------------------------------------
def build_phi(A, B):
    phi = K(1)
    for Z, e in A:
        if Z.pt != INF:
            phi *= (x - Z.pt)**e
    for S, e in B:
        if S.pt != INF:
            phi /= (x - S.pt)**e
    return phi


def numeric_screen(phi, g, d, trials=3):
    Nn = phi.numerator().change_ring(CF)
    Dn = phi.denominator().change_ring(CF)
    h = g * phi.derivative()
    hn = h.numerator().change_ring(CF)
    hd = h.denominator().change_ring(CF)
    hv = lambda t: hn(t) / hd(t)
    rng = [CF(0.3137, 0.2718), CF(-1.1414, 0.5772), CF(0.6931, -1.618)]
    for x0 in rng[:trials]:
        y0 = Nn(x0) / Dn(x0)
        target = hv(x0)
        pts = (Nn - y0 * Dn).roots(CF, multiplicities=False)
        if len(pts) != d:
            return False
        tol = CF(10)**-40 * (1 + target.abs())
        if any((hv(t) - target).abs() > tol for t in pts):
            return False
    return True


def exact_eta(phi, g, d):
    """eta(y) with phi^*(eta(y) dy) = dx/g, or None if C(phi) is not closed"""
    h = g * phi.derivative()
    hn, hd = h.numerator(), h.denominator()
    deg = max(hn.degree(), hd.degree())
    if deg % d:
        return None
    k = deg // d
    N, D = phi.numerator(), phi.denominator()
    basis = [N**i * D**(k - i) for i in range(k + 1)]
    cols = [hn * Bi for Bi in basis] + [-hd * Bi for Bi in basis]
    L = max(c.degree() for c in cols) + 1
    M = matrix(QQbar, L, len(cols),
               lambda r, c: cols[c][r])
    ker = M.right_kernel().basis()
    if not ker:
        return None
    v = ker[0]
    By = sum(v[i] * yv**i for i in range(k + 1))            # coefficients of b
    Ay = sum(v[k + 1 + i] * yv**i for i in range(k + 1))    # coefficients of a
    if Ay == 0 or By == 0:
        return None
    eta = By / Ay        # R(y) = A/B,  eta = dy / R(y)
    # exact verification  phi^* eta = omega
    lhs = K(eta.numerator()(phi)) / K(eta.denominator()(phi)) * phi.derivative()
    if lhs != 1 / g:
        return None
    return eta


def find_pullback(zeros, poles, g):
    dmax = sum(Z.order + 1 for Z in zeros) // 2        # Proposition 3.6
    if dmax < 2:
        return None
    seen = set()
    for d, B in pole_fibres(poles, dmax):
        for A in zero_fibres(zeros, d):
            key = (tuple((id(Z), e) for Z, e in A), tuple((id(S), e) for S, e in B))
            if key in seen:
                continue
            seen.add(key)
            phi = build_phi(A, B)
            if numeric_screen(phi, g, d):
                eta = exact_eta(phi, g, d)
                if eta is not None:
                    return d, A, B, phi, eta
    return None


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------
def classify(rhs, verbose=True):
    g = parse_rhs(rhs)
    zeros, poles = analyse(g)
    out = {'g': g, 'type': None, 'new': None, 'phi': None, 'eta': None}
    L = ["Equation    u' = %s" % pexpr(g, 'u'),
         "1-form      omega = dx / (%s)" % pexpr(g),
         "div(omega) = " + ' '.join('%+d[%s]' % (Z.order, Z.label())
                                    for Z in zeros + poles)]
    for S in poles:
        L.append("   residue at %s (pole of order %d): %s"
                 % (S.label(), S.w, pnum(S.res)))

    typ = classify_type(zeros, poles)
    out['type'] = typ
    L.append("TYPE:    %s type" % typ)

    if typ == 'exact':
        new = (len(poles) == 1 and poles[0].w == 2)
        out['new'] = new
        L.append("NEW/OLD: %s  (exact type is new iff div(omega) = -2P; "
                 "cf. Cor. 3.4)" % ('NEW' if new else 'OLD'))
    elif typ == 'exponential':
        out['new'] = False
        L.append("NEW/OLD: OLD  (exponential type is always old)")
    else:
        cert = None
        if len(zeros) == 1 and is_prime(zeros[0].order + 1):
            cert = "Prop. 5.4: single zero of order m with m+1 prime"
        nz = [S.res for S in poles if S.res != 0]
        if cert is None and len(nz) >= 2 and all(
                ratio_in_QQ(a, b) is None for a, b in itertools.combinations(nz, 2)):
            cert = "Thm. 1.2 (g=0): no two nonzero residues Q-dependent"
        if cert:
            out['new'] = True
            L.append("NEW/OLD: NEW  [%s]" % cert)
        else:
            res = find_pullback(zeros, poles, g)
            if res is None:
                out['new'] = True
                L.append("NEW/OLD: NEW  (no admissible phi of degree >= 2 "
                         "gives a differential subfield C(phi))")
            else:
                d, A, B, phi, eta = res
                out.update(new=False, phi=phi, eta=eta)
                L.append("NEW/OLD: OLD  (proper pullback of degree %d)" % d)
                L.append("   phi(x) = %s" % pexpr(phi))
                L.append("   eta    = (%s) dy" % pexpr(eta, 'y'))
                L.append("   so v = phi(u) solves  v' = %s ;  classify that "
                         "equation to see if it is new" % pexpr(1 / eta, 'y'))
    if verbose:
        print('\n'.join(L))
        print()
    return out


# run from the command line:  sage classify_ode.sage "u^3-u^2" ...
import sys as _sys
if _sys.argv and _sys.argv[0].endswith('classify_ode.sage.py'):
    for _arg in _sys.argv[1:]:
        classify(_arg)
