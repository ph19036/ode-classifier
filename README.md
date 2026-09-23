# ode-classifier

Classify autonomous first-order differential equations

  **u′ = g(u)**, with g a rational function,

by **type** (exact, exponential or general) and as **new** or **old**. When an equation is old, the program returns an explicit substitution v = φ(u) and the simpler equation it comes from.

**Try it online, no installation needed:** https://sites.google.com/view/parthakumbhakar/software

## Background

Every first-order algebraic differential equation f(u, u′) = 0 belongs to one of four types: exact, exponential, Weierstrass or general. An equation is *old* if it comes from a "simpler" first-order equation through an algebraic substitution v = φ(u) of degree at least 2, and *new* otherwise.

Solutions of a new and general type equation cannot be expressed through classical functions, and any distinct nonconstant solutions are algebraically independent over ℂ.

For u′ = g(u) with g rational, Weierstrass type never occurs.

## Reference

P. Kumbhakar, *New and general type meromorphic 1-forms on curves*, Communications in Algebra **54** (2026), no. 5, 1918–1935. https://doi.org/10.1080/00927872.2025.2569453

The classification into types follows M. Noordman, M. van der Put and J. Top, *Autonomous first order differential equations*, Trans. Amer. Math. Soc. **375** (2022), 1653–1670.

## Files

| File | What it is |
|---|---|
| `classify_ode.sage` | Main program for SageMath. Exact arithmetic over the algebraic numbers. |
| `classify_ode.py` | Python version (SymPy + mpmath). Runs without Sage; uses high-precision numerics for some checks. |

## Usage

### SageMath

From a terminal:

```
sage classify_ode.sage "u^2*(u-1)^3*(u-2)^5" "u/(u+1)"
```

Inside a Sage session or Jupyter notebook:

```
load("classify_ode.sage")
classify("(u^5 - u^3)/2")
r = classify("u*(u^2+1)^2/2")   # r['type'], r['new'], r['phi'], r['eta']
```

### Python

```
pip install sympy mpmath
python classify_ode.py "u^3 - u^2" "u/(u+1)"
```

Input: g(u) as a rational function in one variable with numeric coefficients; `I` and `sqrt(...)` are allowed. An input like `u' = u^3 - u^2` also works.

## Examples

| Equation | Result |
|---|---|
| u′ = u²(u−1)³(u−2)⁵ | general type, new (Example 5.1 of the paper) |
| u′ = (u⁵ − u³)/2 | general type, old; φ = u⁻² (Example 5.2) |
| u′ = u³ − u², u′ = u/(u+1) | general type, new (Rosenlicht) |
| u′ = u(u²+1)²/2 | general type, old; v = 1/(u²+1) gives v′ = (v−1)/v |
| u′ = u², u′ = 1 | exact type, new |
| u′ = u³ | exact type, old |
| u′ = u, u′ = u³ − u | exponential type, old |

## Method

The type is read off from the residues of ω = dx/g(x): exact if all residues vanish; exponential if all poles are simple and all residues are rational multiples of one another; general otherwise.

For new/old: if ω = φ\*η with deg φ ≥ 2, then η is of general type and has a zero Q₁ and a pole Q₂. After a Möbius change of the target, Q₁ = 0 and Q₂ = ∞, so

  φ = ∏ (x − P)^{e_P} / ∏ (x − S)^{e_S},

where the P are zeros and the S are poles of ω. The exponents are forced by e_P (ord η + 1) = ord_P ω + 1 (Lemma 3.1), and at simple poles by residue ratios (Lemma 3.2). This leaves finitely many candidates for φ. Each candidate is tested by checking whether C(φ) is a differential subfield, i.e. whether g·φ′ ∈ C(φ).

Unlike Algorithm 5.1 of the paper, this procedure does not rely on the Hurwitz realization problem, so it decides new/old for every rational g.

## Limitations

- Coefficients must be numeric; symbolic parameters are not supported.
- The search grows exponentially with the number of zeros and poles. Typical examples take seconds; large ones can take longer.

## Credits

Written by Partha Kumbhakar with the help of Claude (Anthropic).

## License

MIT License. See `LICENSE`.
