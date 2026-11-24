"""Verification for general identities, exact benchmarks and numerical branches.

Run with python -B code/verify.py from the final report directory.
"""
from dataclasses import replace
import unittest
import numpy as np
import sympy as s

from model import Parameters, from_scaled, growth, growth_prime, rhs
from equilibria import polynomial, physical, cardano, folds
from jacobian import x, y, field, symbolic, parameters, jacobian
from bifurcations import (R, specialization, trace_crossing, hopf_coefficient,
                          m_hopf, k_hopf, dimensional_bt, companion,
                          focal_energy, energy_quartic, rectangle_certificate)
from stability import classify


def is_zero(expression):
    if isinstance(expression,s.MatrixBase):
        return expression.applyfunc(s.factor) == s.zeros(*expression.shape)
    return s.factor(expression) == 0


class Identities(unittest.TestCase):
    def test_equilibrium_and_jacobian(self):
        r,k,al,m,be,e,d = vars(parameters).values()
        F = growth(x,parameters)
        C = parameters.C
        Q = polynomial(x,parameters)
        y_star = e*m*x/d-be
        self.assertTrue(is_zero(field.subs(y,y_star)-s.Matrix([Q,0])))
        v = be+y
        expected = s.Matrix([
            [F+x*F.diff(x)-m*y/v,-m*be*x/v**2],
            [e*m*y/v,e*m*be*x/v**2-d]
        ])
        self.assertTrue(is_zero(symbolic-expected))
        substitute_m = {m:F+C/x}
        J = symbolic.subs(y,y_star).subs(substitute_m)
        T = (x*F.diff(x)-d*F/m).subs(substitute_m)
        det = (-d*F*Q.diff(x)/m).subs(substitute_m)
        l = s.Symbol("l")
        self.assertTrue(is_zero(J.charpoly(l).as_expr()-(l*l-T*l+det)))
        self.assertTrue(is_zero(symbolic.subs({x:0,y:0}).charpoly(l).as_expr()
                                -(l-r)*(l+d)))
        self.assertTrue(is_zero(symbolic.subs({x:k,y:0}).charpoly(l).as_expr()
                                -(l+r*(1+al*k))*(l-e*m*k/be+d)))

    def test_lyapunov_and_scaled_divergence(self):
        r,k,al,m,be,e,d = vars(parameters).values()
        F = growth(x,parameters)
        f,g = field
        self.assertTrue(is_zero((1-k/x)*f+g/e
                         +r/k*(x-k)**2*(1+al*x)-y*(m*k/(be+y)-d/e)))
        s0,z0 = s.symbols("s0 z0",positive=True)
        F0 = F.subs(x,s0)
        equilibrium = {m:F0*(be+z0)/z0,d:e*F0*s0/z0}
        B = be/(e*(be+z0))
        entropy = (1-s0/x)*f+B*(1-z0/y)*g
        target = (x-s0)*(F-F0)-B*d*(y-z0)**2/(be+y)
        self.assertTrue(is_zero((entropy-target).subs(equilibrium)))
        X,Y,A,M,R0,D = s.symbols("X Y A M R D",positive=True)
        p = (1-X)*(1+A*X)
        scale = {x:k*X,y:be*Y,al:A/k,m:r*M,d:r*D,e:be*D*R0/(M*k)}
        sc = s.Matrix([X*(p-M*Y/(1+Y)),D*Y*(R0*X/(1+Y)-1)])
        self.assertTrue(is_zero(s.Matrix([f/(k*r),g/(be*r)]).subs(scale,simultaneous=True)-sc))
        for q, expected in [
            ((1+Y)/(X*Y*p),(M*X*p.diff(X)-D*p)/(X*p*p)),
            (s.exp(-(A-1)*X)*(1+Y)/(X*Y),
             s.exp(-(A-1)*X)*((p.diff(X)-(A-1)*p)*(1+Y)/Y+(A-1)*M-D/X))
        ]:
            self.assertTrue(is_zero((q*sc[0]).diff(X)+(q*sc[1]).diff(Y)-expected))

    def test_parameter_derivatives_and_root_multiplicity(self):
        r,k,al,m,be,e,d = vars(parameters).values()
        Q = polynomial(x,parameters)
        F = growth(x,parameters)
        expected = (r*x*x*(1-x/k),d/e,-x,r*x*x*(1+al*x)/k**2,be/e)
        for parameter, partial in zip((al,be,m,k,d),expected):
            self.assertTrue(is_zero(Q.diff(parameter)-partial))
        self.assertTrue(is_zero(s.Matrix([Q,Q.diff(x)]).jacobian([m,be]).det()-d/e))
        L = k-1/al
        a = r*al/k
        at = {x:L/3,be:e*a*L**3/(27*d),m:r+a*L**2/3}
        self.assertTrue(all(is_zero(Q.diff(x,n).subs(at)) for n in range(3)))
        self.assertTrue(is_zero(Q.diff(x,3)+6*a))
        # Algebraic Cardano pairing, with U**3 satisfying the resolvent.
        U,P,S = s.symbols("U P S",nonzero=True)
        z = U-P/(3*U)
        numerator = s.expand(U**3*(z**3+P*z+S))
        self.assertEqual(numerator,U**6+S*U**3-P**3/27)

    def test_center_expansions(self):
        # At R=1 the linear graph slope and the quadratic predator drift.
        A,M,D,V = s.symbols("A M D V",positive=True)
        slope = -M/(1+A)
        X = 1+slope*V
        self.assertTrue(is_zero(s.diff(X*((1-X)*(1+A*X)-M*V/(1+V)),V).subs(V,0)))
        drift = D*V*(X/(1+V)-1)
        self.assertTrue(is_zero(drift.diff(V,2).subs(V,0)/2+D*(1+M/(1+A))))
        # Formal coefficient matching in the companion invariance equation.
        b2,b3,T,C2,C3,L = s.symbols("b2 b3 T C2 C3 L")
        H = b2*V**2+b3*V**3
        defect = s.expand(C2*V**2+C3*V**3+(T+L*V)*H-H.diff(V)*H)
        self.assertEqual(s.solve(defect.coeff(V,2),b2)[0],-C2/T)
        self.assertEqual(s.solve(defect.coeff(V,3).subs(b2,0),b3)[0],-C3/T)


class Benchmarks(unittest.TestCase):
    def test_cardano_and_root_count(self):
        base = Parameters(*map(R,(7,7,1,16,2,1,1)))
        for beta, count in ((2,3),(4,2),(20,1),(112,0)):
            p = replace(base,beta=R(beta))
            self.assertEqual(len(physical(p)),count)
            for z in cardano(p):
                self.assertLess(abs(complex(polynomial(z,p).evalf(60))),1e-45)
                if abs(complex(z.evalf(60)).imag) < 1e-45 and p.C/p.m < s.re(z.evalf(60)) < p.k:
                    z0=(s.re(z.evalf(60)),p.e*p.m*s.re(z.evalf(60))/p.d-p.beta)
                    self.assertLess(max(map(abs,rhs(0,z0,p))),1e-45)
        cusp = Parameters(1,1,R(10),R(37,10),R(27,100),1,1)
        self.assertEqual([mu for _,mu in physical(cusp)],[3])
        self.assertEqual(cardano(cusp),[R(3,10)]*3)
        self.assertEqual(len(folds(base)),2)
        self.assertEqual(folds(cusp),[])
        no_allee = Parameters(1,1,R(1),R(3),R(2,5),1,1)
        self.assertEqual(len(physical(no_allee)),1)
        self.assertEqual(folds(no_allee),[])
        # At R=1 the axial root is excluded despite zero prey-polynomial residual.
        axial = replace(no_allee,beta=R(3))
        self.assertEqual(physical(axial),[])

    def test_grid_against_turning_point_classification(self):
        for A in (R(1,2),R(1),R(2),R(10)):
            for C in (R(1,500),R(1,25),R(1,5),R(27,100),R(2)):
                p = Parameters(1,1,A,R(1),C,1,1)
                vertices = folds(p)
                for M in (R(1,200),R(3,2),R(3),R(19,5),R(8)):
                    q = replace(p,m=M)
                    count = 0 if M <= C else 1
                    if vertices and vertices[0][1] < M < vertices[1][1]:
                        count = 3
                    self.assertEqual(len(physical(q)),count,(A,C,M))

    def test_hopf_benchmarks(self):
        for p,point,path,coefficient,det,crossing in (
            (m_hopf,(R(1,5),R(6,25)),"m",-R(1525,168),R(7,5),R(61,168)),
            (k_hopf,(R(1,10),R(162,1855)),"k",-R(1415,252),R(49,25),R(601,2520)),
        ):
            self.assertTrue(is_zero(field.subs(specialization(p)|dict(zip((x,y),point)))))
            c,w = hopf_coefficient(p,point)
            self.assertEqual((c,w**2),(coefficient,det))
            J = symbolic.subs(specialization(p)|dict(zip((x,y),point)))
            # The real ellipse radius corresponds to |complex amplitude| / |p* e_1|.
            basis_factor = (1+(J[0,0]/w)**2)/2
            self.assertEqual(energy_quartic(p,point),coefficient*basis_factor)
            self.assertEqual(trace_crossing(p,point[0],path),crossing)
            z = physical(p)[0][0]
            self.assertEqual(classify(z,p)[0],"imaginary pair")
            eps = 1e-5
            q1 = replace(p,**{path:float(getattr(p,path))-eps})
            q2 = replace(p,**{path:float(getattr(p,path))+eps})
            T1,T2 = [np.trace(jacobian(physical(q)[0][0],q)) for q in (q1,q2)]
            self.assertAlmostEqual((T2-T1)/(2*eps),float(crossing),places=7)
        p = m_hopf
        F = growth(x,p)
        H = (x*F+p.C)*F.diff(x)-p.d*F
        cubic = 1000*x**3-1150*x**2+175*x-58
        self.assertTrue(is_zero(25*H-(5*x-1)*cubic))
        self.assertEqual(s.discriminant(cubic,x),-214501937500)

    def test_bt_benchmarks(self):
        p = dimensional_bt
        s0,z0 = R(1,5),R(144,425)
        at = specialization(p)|{x:s0,y:z0}
        J = symbolic.subs(at)
        self.assertTrue(is_zero(field.subs(at)))
        self.assertTrue(is_zero(J**2))
        self.assertEqual(J.rank(),1)
        self.assertTrue(is_zero(polynomial(x,p)+10*(x-s0)**2*(x-R(1,2))))
        wrong = replace(p,m=R(5))
        self.assertTrue(is_zero(-polynomial(x,wrong).diff(x)-30*(x-R(3,10))**2-R(13,10)))
        ms,ks = parameters.m,parameters.k
        q = replace(p,m=ms,k=ks)
        self.assertEqual(companion(q,s0,(ms,p.m),(ks,R(1))), (3,-R(13,12),R(25,12),-R(271,1224)))
        RR,DD = s.symbols("RR DD",positive=True)
        self.assertEqual(companion(from_scaled(10,R(5,2),RR,DD),R(1,10),(RR,R(250,7)),(DD,R(35,36))),
                         (R(21,5),R(41,18),R(35,9),R(3087,3125000)))

    def test_bautin_and_global_cycle_rectangle(self):
        h = s.Symbol("h",positive=True)
        H = R(522,449)
        p = from_scaled(10,R(9,5)*(1+h)/h,10*(1+h),R(7,10)*(1+h)/h)
        c4 = energy_quartic(p,(R(1,10),h))
        self.assertTrue(is_zero(c4-5*(449*h-522)/(2*(7*h-18)**2)))
        self.assertEqual(c4.diff(h).subs(h,H),R(452594245,39214368))
        self.assertEqual((-h/(2*(1+h))).subs(h,H),-R(261,971))
        p0 = Parameters(*(s.sympify(v).subs(h,H) for v in vars(p).values()))
        w2, focal = focal_energy(p0,(R(1,10),H),6)
        self.assertEqual((w2,focal), (R(861,1450),{4:0,6:-R(364732858625,1808762724)}))
        self.assertEqual(list(rectangle_certificate().values()),
                         [R(54247,1152),R(42801,896),R(29285,1152),R(23715,896)])


if __name__ == "__main__":
    unittest.main(verbosity=2)

