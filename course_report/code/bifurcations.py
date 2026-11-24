"""Exact SymPy calculations in the conventions of the paper."""
import sympy as s
from model import Parameters, growth, growth_prime, from_scaled
from jacobian import x, y, field, symbolic, parameters

R = s.Rational
m_hopf = Parameters(1, 1, 10, R(24,5), R(6,25), 1, 2)
k_hopf = Parameters(1, 1, 10, R(53,10), R(9,53), 1, R(371,180))
dimensional_bt = Parameters(1, 1, 10, R(17,5), R(12,85), 1, R(17,12))


def specialization(p):
    return dict(zip(vars(parameters).values(), vars(p).values()))


def hopf_coefficient(p, equilibrium):
    """Complex eigenvector formula, original time and q_x=1."""
    substitutions = specialization(p) | dict(zip((x,y), equilibrium))
    J = symbolic.subs(substitutions)
    omega = s.sqrt(J.det())
    assert J.trace() == 0 and omega > 0
    q = s.Matrix([1, (s.I*omega-J[0,0])/J[0,1]])
    projection = s.Matrix.hstack(q, s.conjugate(q)).inv()[0,:]
    assert s.simplify(J*q-s.I*omega*q) == s.zeros(2,1)
    vector = [x,y]

    def form(*args):
        from itertools import product
        return s.Matrix([
            sum(component.diff(*[vector[j] for j in indices]).subs(substitutions)
                * s.prod(v[j] for v, j in zip(args, indices))
                for indices in product(range(2), repeat=len(args)))
            for component in field
        ]).applyfunc(s.simplify)

    qb = s.conjugate(q)
    g21 = projection * (
        form(q,q,qb)
        -2*form(q, J.inv()*form(q,qb))
        +form(qb, (2*s.I*omega*s.eye(2)-J).inv()*form(q,q))
    )
    return s.simplify(s.re(g21[0])/2), omega


def trace_crossing(p, prey, parameter):
    F = growth(x, parameters)
    Q = x*(F-parameters.m)+parameters.C
    T = x*F.diff(x)-parameters.d*F/parameters.m
    mu = getattr(parameters, parameter)
    derivative = T.diff(mu)-T.diff(x)*Q.diff(mu)/Q.diff(x)
    return s.factor(derivative.subs(specialization(p) | {x: prey}))


def companion(p, prey, parameter1, parameter2):
    """Jet and regularity determinant in the (x, f) coordinates."""
    v = s.Symbol("v", real=True)
    F = growth(x, p)
    theta = F-v/x
    gap = p.m-theta
    w = (v/x+x*F.diff(x))*v-(x*theta*gap/p.m)*(p.e*x*gap/p.beta-p.d)
    variables = (parameter1[0], parameter2[0])
    at = {x:prey, v:0, parameter1[0]:parameter1[1], parameter2[0]:parameter2[1]}
    def derivative(*indices):
        return s.factor(w.diff(*indices).subs(at))
    assert s.factor(w.subs(at)) == derivative(x) == derivative(v) == 0
    a, b, c = derivative(x,x)/2, derivative(x,v), derivative(v,v)/2
    first = [derivative(mu) for mu in variables]
    second = [derivative(v,mu)-b*derivative(x,mu)/(2*a) for mu in variables]
    return a, b, c, s.factor(s.Matrix([first,second]).det())


def focal_energy(p, point, degree):
    """Independent real focal computation using a homogeneous polynomial invariant."""
    subs = specialization(p) | dict(zip((x,y), point))
    J = symbolic.subs(subs)
    omega2 = J.det()
    u, v, h = s.symbols("u v h", real=True)
    basis = s.Matrix.hstack(s.Matrix([1,0]), J[:,0])
    base_field = field.subs(specialization(p))
    translated = s.Matrix(point)+h*basis*s.Matrix([u,v])
    expanded = basis.inv()*base_field.subs(dict(zip((x,y),translated)), simultaneous=True)
    jets = [s.zeros(2,1)] + [
        expanded.applyfunc(lambda value: s.Poly(s.series(value,h,0,degree).removeO(),h)
                           .nth(j).expand())
        for j in range(1,degree)
    ]
    H2 = u*u+omega2*v*v
    energies = {2:H2}
    focal = {}
    for n in range(3,degree+1):
        coefficients = s.symbols(f"a0:{n+1}")
        trial = sum(coefficients[i]*u**(n-i)*v**i for i in range(n+1))
        defect = s.Matrix([trial.diff(u), trial.diff(v)]).dot(jets[1])
        for j in range(2,n):
            H = energies[j]
            defect += s.Matrix([H.diff(u), H.diff(v)]).dot(jets[n+1-j])
        unknowns = coefficients
        equations = []
        if n % 2 == 0:
            resonant = s.Symbol("resonant")
            defect -= resonant*H2**(n//2)
            unknowns += (resonant,)
            equations = [coefficients[0]]
        equations += [s.expand(defect).coeff(u,n-i).coeff(v,i) for i in range(n+1)]
        solution = s.solve(equations, unknowns)
        energies[n] = trial.subs(solution)
        if n % 2 == 0:
            focal[n] = s.factor(solution[resonant])
            if focal[n] != 0:
                break
    return omega2, focal


def rectangle_certificate():
    """Exact Bernstein positivity over the closed rectangle of Section 5."""
    X, D, U = s.symbols("X D U")
    p = 1+9*X-10*X**2
    Q = X*(p-12)+12*U
    N = 12*X*p.diff(X)-D*p
    W = N.diff(X)*Q-N*Q.diff(X)
    assert s.Poly(W,D,U).degree(D) <= 1 and s.Poly(W,D,U).degree(U) <= 1
    minima = {}
    z = s.Symbol("z")
    for d0 in (R(5,2), R(7,2)):
        for r0 in (R(27,5), R(28,5)):
            subs = {D:d0,U:1/r0}
            lo, hi = R(21,100), R(27,100)
            assert Q.subs(subs | {X:lo}) > 0 > Q.subs(subs | {X:hi})
            assert all(N.subs(subs | {X:q}) > 0 for q in (lo,hi))
            polynomial = W.subs(subs)
            n = s.degree(polynomial,X)
            coefficients = []
            for i in range(8):
                monomial = s.Poly(polynomial.subs(X,(i+z)/8),z)
                coefficients.extend(
                    sum(monomial.nth(j)*s.binomial(k,j)/s.binomial(n,j)
                        for j in range(k+1)) for k in range(n+1))
            minima[d0,r0] = min(coefficients)
            assert minima[d0,r0] > 0
    return minima



def energy_quartic(p, point):
    """Real planar cubic formula, twice the radial coefficient in the unit ellipse basis."""
    at = specialization(p) | dict(zip((x,y), point))
    J = symbolic.subs(at).applyfunc(s.factor)
    omega = s.sqrt(s.factor(J.det()))
    u, v = s.symbols("u v", real=True)
    basis = s.Matrix.hstack(s.Matrix([1,0]), J[:,0]/omega)
    shift = basis*s.Matrix([u,v])
    jets = []
    for n in (2,3):
        terms = sum(
            (field.diff(x,i).diff(y,n-i).subs(at).applyfunc(s.factor)
             *shift[0]**i*shift[1]**(n-i)/(s.factorial(i)*s.factorial(n-i))
             for i in range(n+1)), s.zeros(2,1)
        )
        jets.append((basis.inv()*terms).applyfunc(s.expand))
    f, g = jets[0]
    cubic_f, cubic_g = jets[1]
    f20, f11, f02 = f.diff(u,2), f.diff(u,v), f.diff(v,2)
    g20, g11, g02 = g.diff(u,2), g.diff(u,v), g.diff(v,2)
    cubic = cubic_f.diff(u,3)+cubic_f.diff(u,v,v)+cubic_g.diff(u,u,v)+cubic_g.diff(v,3)
    quadratic = f11*(f20+f02)-g11*(g20+g02)-f20*g20+f02*g02
    return s.factor((cubic+quadratic/omega)/8)

