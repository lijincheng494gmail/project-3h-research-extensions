"""Exact Cartesian checks for the second crossing and matched mixed-model examples."""

import json
from pathlib import Path

import sympy as sp

x, y, K, b, c, a = sp.symbols("x y K b c a", positive=True)
checks = {}


def equals(name, actual, expected):
    difference = sp.simplify(sp.factor(actual - expected))
    if difference != 0:
        raise AssertionError((name, difference))
    checks[name] = str(expected)


ratio = sp.Rational(5, 6)
load_capacity = 6 * x * (1 + x * x) / (1 + 6 * x * x)
feed = 110 * x * y / (65 * x + 54 * y)
system = sp.Matrix([x * (1 + x * x) * (1 - x / K) - feed, feed - y])
jac = system.jacobian((x, y))
on_branch = {K: load_capacity, y: ratio * x}
trace = sp.factor(jac.trace().subs(on_branch))
det = sp.factor(jac.det().subs(on_branch))
equals(
    "trace on the whole positive branch",
    trace,
    -(3 * x * x - 1) * (4 * x * x - 1) / (12 * (1 + x * x)),
)
equals(
    "determinant on the whole positive branch",
    det,
    3 * (6 * x**4 - 3 * x * x + 1) / (44 * (1 + x * x)),
)
slope = sp.diff(trace, x) / sp.diff(load_capacity, x)
second_root = sp.sqrt(3) / 3
equals(
    "second crossing capacity", load_capacity.subs(x, second_root), 8 * sp.sqrt(3) / 9
)
equals("second crossing trace", trace.subs(x, second_root), 0)
equals("second crossing determinant", det.subs(x, second_root), sp.Rational(3, 88))
equals(
    "second crossing trace derivative", slope.subs(x, second_root), -3 * sp.sqrt(3) / 32
)

feed = a * x * y / (1 + b * x + c * y)
system = sp.Matrix([x * (1 + x) * (1 - x / K) - feed, feed - y])
at = {a: 1 + b + c, x: 1, y: 1, K: 2}
jac = system.jacobian((x, y))
matrix = jac.subs(at)
direction = -matrix.inv() * system.diff(K).subs(at)
total = jac.trace().diff(K).subs(at) + sum(
    jac.trace().diff(coord).subs(at) * tangent
    for coord, tangent in zip((x, y), direction)
)
equals("mixed determinant", matrix.det(), (c + 2) / (2 * (b + c + 1)))
equals(
    "mixed trace derivative",
    total,
    -(3 * b * c - 10 * b + 3 * c * c + c - 6) / (4 * (c + 2) * (b + c + 1)),
)
for label, bv, cv, target in [
    ("P0+", 0, 1, sp.Rational(1, 12)),
    ("P0-", 0, 2, -sp.Rational(1, 6)),
    ("P3+", 1, 1, sp.Rational(1, 4)),
    ("P3-", 1, 3, -sp.Rational(23, 100)),
]:
    point = {b: bv, c: cv}
    equals(label, total.subs(point), target)
    assert matrix.det().subs(point) > 0
path = Path(__file__).with_name("branch_identities.json")
path.write_text(json.dumps(checks, indent=2) + "\n")
print(f"{len(checks)} exact branch and comparison identities passed.")
