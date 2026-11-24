import Direction2
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
namespace Direction2.Params
variable (p : Params)

/-- Determinant of the Cartesian matrix obtained by differentiating the two original equations. -/
def cartesianDet (g : ℝ → ℝ) (h x y : ℝ) :=
  deriv (fun u => p.preyRHS g u y) x * deriv (fun v => p.predatorRHS h x v) y -
    deriv (fun v => p.preyRHS g x v) y * deriv (fun u => p.predatorRHS h u y) x

theorem cartesian_det_eq {g : ℝ → ℝ} {h x y : ℝ}
    (root : p.Root g h x y) (hy : 0 < y) (hg : DifferentiableAt ℝ g x) :
    p.cartesianDet g h x y = p.detJ g h x y := by
  have nb := (add_pos p.hβ hy).ne'
  have gval : g x = p.intake y := (eq_div_iff nb).2 root.1
  have pval : p.e*p.m*x/(p.β+y) = p.d+h*y := (div_eq_iff nb).2 (by linarith only [root.2])
  have identX : HasDerivAt (fun u : ℝ => u) 1 x := hasDerivAt_id x
  have identY : HasDerivAt (fun v : ℝ => v) 1 y := hasDerivAt_id y
  have den := (hasDerivAt_const y p.β).add identY
  have hd : HasDerivAt p.intake ((p.m*(p.β+y)-p.m*y)/(p.β+y)^2) y := by
    convert (identY.const_mul p.m).div den nb using 1
    simp [intake]
  have xx := (identX.mul (hg.hasDerivAt.sub_const (p.intake y))).deriv
  change deriv (fun u => p.preyRHS g u y) x = _ at xx
  have xy := (((hasDerivAt_const y (g x)).sub hd).const_mul x).deriv
  change deriv (fun v => p.preyRHS g x v) y = _ at xy
  have yx := ((((identX.const_mul (p.e*p.m)).div_const (p.β+y)).sub_const p.d).const_mul y
    |>.sub_const (h*y^2)).deriv
  change deriv (fun u => p.predatorRHS h u y) x = _ at yx
  have yy := ((identY.mul (((hasDerivAt_const y (p.e*p.m*x)).div den nb).sub_const p.d)).sub
    ((identY.pow 2).const_mul h)).deriv
  change deriv (fun v => p.predatorRHS h x v) y = _ at yy
  unfold cartesianDet detJ
  rw [xx, xy, yx, yy]
  simp [id, gval, pval]
  field_simp [nb]
  ring

#print axioms cartesian_det_eq
end Direction2.Params
