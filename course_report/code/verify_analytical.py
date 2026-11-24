"""Exact polynomial, Taylor-jet and parameter-derivative checks for the analytical paper."""
import unittest

import sympy as sp


class AnalyticalFamilies(unittest.TestCase):
    def zero(self, expression):
        self.assertEqual(sp.factor(expression), 0)

    def test_hopf_polynomials_and_global_cycle_bound(self):
        z, h, t, b, P, s, D = sp.symbols("z h t b P s D", positive=True)
        X = s*(1 + z)
        p = P*(1 + t*z - b*z**2)
        M, R = P*(1 + h)/h, (1 + h)/s
        DH = M*t
        Q = X*(p-M) + M/R
        N = M*X*p.diff(z)/s - D*p
        q1, q2 = t-1/h, t-b
        n1, n2 = t-t**2-2*b, b*(t-2)
        S = n2*q1-n1*q2
        self.zero(Q - s*P*z*(q1+q2*z-b*z**2))
        self.zero(N.subs(D, DH) - M*P*z*(n1+n2*z))
        W = (N.diff(z)*Q-N*Q.diff(z))/s
        WH = W.subs(D, DH)
        self.zero(WH - M*P**2*z**2*(S+2*b*n1*z+b*n2*z**2))
        correction = (p.diff(z)*Q-p*Q.diff(z))/s
        self.zero(W-WH-(DH-D)*correction)
        self.zero(sp.limit(correction/M, h, 0) - P*(1+b*z**2))
        self.zero(N.subs(z, 0)/M + (D-DH)*h/(1+h))

    def test_cubic_focus_from_cartesian_normal_form(self):
        # Divide time by the positive growth scale P and use the linear coordinates
        # (x,y) with z=x, v=(Y-h)/h=(1+h)(t*x+omega*y). Rotation is counterclockwise.
        x, y, h, t, b, omega = sp.symbols("x y h t b omega", positive=True)
        v = (1+h)*(t*x+omega*y)
        # u = h*v/(1+h) and (1+u)^(-1) through degree three.
        u = h*v/(1+h)
        degrees = sp.symbols("epsilon")
        def jet(expr):
            polynomial = sp.Poly(expr.subs({x:degrees*x, y:degrees*y}), degrees)
            return sp.Add(*(polynomial.nth(j) for j in range(4)))
        inv = 1-u+u**2-u**3
        f = jet((1+x)*(1+t*x-b*x**2-(1+v)*inv))
        vdot = jet((1+h)*t/h*(1+v)*(x-u)*inv)
        g = (vdot/(1+h)-t*f)/omega
        def deriv(expr, nx, ny):
            return sp.factor(expr.diff(x, nx).diff(y, ny).subs({x:0, y:0}))
        fxx, fxy, fyy = (deriv(f, *order) for order in [(2,0),(1,1),(0,2)])
        gxx, gxy, gyy = (deriv(g, *order) for order in [(2,0),(1,1),(0,2)])
        cubic = deriv(f,3,0)+deriv(f,1,2)+deriv(g,2,1)+deriv(g,0,3)
        correction = fxy*(fxx+fyy)-gxy*(gxx+gyy)-fxx*gxx+fyy*gyy
        sixteen_l1 = sp.factor(cubic+correction/omega)
        omega_sq = t*(1/h-t)
        result = sp.factor(sixteen_l1.subs(omega**2, omega_sq))
        S = b*(t-2)*(t-1/h)-(t-t**2-2*b)*(t-b)
        self.zero(result + 2*S/(1/h-t))

    def test_bautin_and_fifth_order_damping(self):
        z, xi, t, b, q1, q2, n1, n2, h = sp.symbols(
            "z xi t b q1 q2 n1 n2 h", nonzero=True)
        factor = (n1+n2*z)/(q1+q2*z-b*z**2)
        S = n2*(t-1/h)-n1*q2
        self.zero(S.diff(h)-n2/h**2)
        L = factor.subs(n2,n1*q2/q1)
        self.zero(L.diff(z).subs(z,0))
        L2 = L.diff(z,2).subs(z,0)
        self.zero(L2-2*b*n1/q1**2)
        self.zero(L.diff(z,3).subs(z,0)/L2+3*q2/q1)
        # K_z(0)=t(1+h); keep exactly the jet needed by g''/g'.
        gjet = (q1*z+q2*z**2)*sp.exp(-t*(1+h)*z)/((1+z)*(1-h*t*z+h*b*z**2)**2)
        self.zero(gjet.diff(z,2).subs(z,0)/gjet.diff(z).subs(z,0)
                  -2*(q2/q1-1-t+t*h))
        g1, g2, ell2, ell3 = sp.symbols("g1 g2 ell2 ell3", positive=True)
        inverse = xi/sp.sqrt(g1)-g2*xi**2/(6*g1**2)
        xi_squared = g1*inverse**2 + g2*inverse**3/3
        self.zero(xi_squared.expand().coeff(xi,3))
        dF = xi*(ell2*inverse**2/2+ell3*inverse**3/6)
        self.zero(dF.expand().coeff(xi,4)/5-(g1*ell3-g2*ell2)/(30*g1**sp.Rational(5,2)))
        angle = sp.symbols("angle", real=True)
        for power, mean in [(4,sp.Rational(3,8)),(6,sp.Rational(5,16))]:
            self.zero(sp.integrate(sp.cos(angle)**power,(angle,0,2*sp.pi))/(2*sp.pi)-mean)

    def test_companion_jet_and_dimensional_unfolding(self):
        x, v, s, P, j, c, m, d, beta, e = sp.symbols("x v s P j c m d beta e", nonzero=True)
        F = P+j*(x-s)+c*(x-s)**2/2
        theta = F-v/x
        w = ((v/x+x*F.diff(x))*v
             -x*theta*(m-theta)/m*(e*x*(m-theta)/beta-d))
        Q = x*(F-m)+d*beta/e
        K = e*x*F*(m-F)/(m*beta)
        self.zero(w.subs(v,0)-K*Q)
        m0 = P+s*j
        d0 = m0*s*j/P
        family = {x:s, v:0, m:m0, d:d0, beta:e*s**2*j/d0}
        jet = lambda a, b: w.diff(x,a).diff(v,b).subs(family)
        self.zero(jet(0,0))
        self.zero(jet(1,0))
        self.zero(jet(0,1))
        self.zero(jet(2,0)-s*j*(2*j+s*c))
        self.zero(jet(1,1)-(j+s*c-d0*j/m0))
        self.zero(w.diff(m).subs(family)+s**2*j)
        r, k, alpha = sp.symbols("r k alpha", positive=True)
        growth = r*(1-s/k)*(1+alpha*s)
        slope, curve = growth.diff(s), growth.diff(s,2)
        mk = growth.diff(k)
        sk = -s*slope.diff(k)/(2*slope+s*curve)
        fold_rate = (s*slope.diff(k)-d0/m0*mk+d0*P/m0**2*mk
                     +(j+s*c-d0*j/m0)*sk)
        normalized = fold_rate.subs({P:growth, j:slope, c:curve})/s
        self.zero(sp.limit(normalized, s, 0)-r/(2*k**2))

    def test_enrichment_and_predation_crossings(self):
        s, m, P, j, c, r, k, alpha = sp.symbols("s m P j c r k alpha", nonzero=True)
        growth = r*(1-s/k)*(1+alpha*s)
        self.zero((growth.diff(s)/growth).diff(k)-1/(k-s)**2)
        Qx = P+s*j-m
        Tx = j+s*c-s*j**2/P
        Fk, jk = sp.symbols("Fk jk")
        total_k = s*jk - s*j*Fk/P - Tx*s*Fk/Qx
        self.zero(sp.limit(total_k, m, sp.oo)-s*(jk-j*Fk/P))
        total_m = s*j/m + Tx*s/Qx
        self.zero(sp.limit(m*total_m,m,sp.oo)-s**2*(j**2/P-c))

    def test_cusp_coordinates(self):
        a,L,m,r,C,z = sp.symbols("a L m r C z", nonzero=True)
        pc = (m-r)/a - L**2/3
        qc = -2*L**3/27+L*(m-r)/(3*a)-C/a
        self.zero(sp.Matrix([-pc,-qc]).jacobian([m,C]).det()+1/a**2)
        self.zero(sp.discriminant(z**3+pc*z+qc,z)+4*pc**3+27*qc**2)

    def test_global_classification_thresholds(self):
        A, M, R, D, X, r, k = sp.symbols("A M R D X r k", positive=True)
        p = (1-X)*(1+A*X)
        H = M*X*p.diff(X)/p
        N = M*X*p.diff(X)-D*p
        self.zero(N/M-p*(H-D)/M)
        self.zero(N.diff(X).subs(D,H)-p*H.diff(X))
        peak = (A-1)/(2*A)
        self.zero(p.subs(X,peak)-(A+1)**2/(4*A))
        alpha_root = sp.symbols("alpha_root", positive=True)
        critical_x = (alpha_root-1)/(alpha_root**2+alpha_root)
        scaled_slope = H.subs(A,alpha_root**2)/M
        self.zero(scaled_slope.diff(X).subs(X,critical_x))
        self.zero(scaled_slope.subs(X,critical_x)-(alpha_root-1)**2/(alpha_root**2+1))
        quadratic = (A-1)*M*X-(A+1)*X**2
        self.zero(quadratic.diff(X).subs(X,(A-1)*M/(2*(A+1))))
        xi, m, d = k/R, r*M, r*D
        floor = xi/2*(xi/(2*k))**(2*m/d)
        self.zero(floor/k-(1/(2*R))**(1+2*M/D))


if __name__ == "__main__":
    unittest.main(verbosity=2)
