import Direction1

open Filter Topology Direction1

namespace D1Example
noncomputable section

def growth (x : ℝ) := 1 + x^2
def intake (z : ℝ) := 110 / (65 + 54*z)

theorem growth_deriv (x : ℝ) : HasDerivAt growth (2*x) x := by
  convert (hasDerivAt_const x (1:ℝ)).add ((hasDerivAt_id x).pow 2) using 1
  simp [growth, id]

theorem growth_deriv₂ (x : ℝ) : HasDerivAt (deriv growth) 2 x := by
  have hg : deriv growth = (fun t : ℝ => 2*t) := funext (fun t => (growth_deriv t).deriv)
  rw [hg]
  simpa using ((hasDerivAt_id x).const_mul (2 : ℝ))

theorem intake_deriv_at_ratio : HasDerivAt intake (-(27/55 : ℝ)) (5/6) := by
  convert (hasDerivAt_const (5/6:ℝ) (110:ℝ)).div
    ((hasDerivAt_const (5/6:ℝ) (65:ℝ)).add ((hasDerivAt_id (5/6:ℝ)).const_mul 54))
    (by norm_num) using 1
  norm_num [intake, id]

theorem exact_intake_admissible : Admissible intake := by
  constructor
  · apply contDiffOn_const.div (contDiffOn_const.add (contDiffOn_const.mul contDiffOn_id))
    intro x hx
    have hx' : 0 < x := hx
    positivity
  · intro x hx
    unfold intake
    positivity
  · intro x hx y hy hxy
    have hx' : 0 < x := hx
    unfold intake
    exact div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)

theorem exact_curvature :
    deriv (deriv (fun x => (growth x)⁻¹)) (1/2) = -(32/125 : ℝ) := by
  rw [D1Core.reciprocal_curvature (by norm_num [growth])
    (Filter.Eventually.of_forall (fun t => (growth_deriv t).differentiableAt))
    (growth_deriv₂ _).differentiableAt, (growth_deriv _).deriv, (growth_deriv₂ _).deriv]
  norm_num [D1Core.curvature, growth]

theorem exact_equilibrium : equilibrium growth intake 1 1 (3/2) (1/2) (5/12) := by
  norm_num [equilibrium,prey,predator,q,growth,intake]

theorem exact_matrix : jac growth intake 1 1 (3/2) (1/2) (5/12) =
    ⟨9/22,-(13/22),15/44,-(9/22)⟩ := by
  have hj := jac_on_ray (g := growth) (p := intake) (e := 1) (d := 1) (K := 3/2)
    (x := 1/2) (r := 5/6) (by norm_num) (growth_deriv _).differentiableAt
    intake_deriv_at_ratio.differentiableAt (by norm_num [intake]) (by norm_num [q,growth,intake])
  rw [intake_deriv_at_ratio.deriv] at hj
  norm_num [qx,(growth_deriv _).deriv,growth,intake] at hj
  exact hj

theorem exact_trace_det :
    (jac growth intake 1 1 (3/2) (1/2) (5/12)).trace = 0 ∧
    (jac growth intake 1 1 (3/2) (1/2) (5/12)).det = 3/88 := by
  rw [exact_matrix]
  norm_num [Jacobian2.trace, Jacobian2.det]

theorem exact_enrichment :
    cap growth (5/6) (1/2) = 3/2 ∧
    (deriv (cap growth (5/6)) (1/2))⁻¹ = 5/3 ∧
    slopeK growth intake 1 1 (5/6) (5/6) (1/2) = 1/9 := by
  have hK := (capacity_deriv (g := growth) (Q := 5/6) (x := 1/2)
    (by norm_num [growth]) (by norm_num [growth]) (growth_deriv _).differentiableAt).deriv
  have hT := (ray_deriv (g := growth) (p := intake) (e := 1) (d := 1) (r := 5/6)
    (Q := 5/6) (s := 1/2) (by norm_num) (by norm_num [growth]) (by norm_num [growth])
    (Filter.Eventually.of_forall (fun t => (growth_deriv t).differentiableAt))
    (growth_deriv₂ _).differentiableAt intake_deriv_at_ratio.differentiableAt
    (by norm_num [intake]) (by norm_num [intake])).deriv
  unfold slopeK
  rw [hK,hT]
  norm_num [Direction1.cap,D,E,D1Core.elasticityPrime,(growth_deriv _).deriv,(growth_deriv₂ _).deriv,growth]

theorem exact_physical_trace :
    ∃ X : ℝ → ℝ, X (3/2) = 1/2 ∧
      (∀ᶠ k in 𝓝 (3/2 : ℝ), 0 < X k ∧ equilibrium growth intake 1 1 k (X k) ((5/6)*X k)) ∧
      HasDerivAt (fun k => (jac growth intake 1 1 k (X k) ((5/6)*X k)).trace) (1/9) (3/2) := by
  have hc : ContDiffAt ℝ 2 growth (1/2) := contDiffAt_const.add (contDiffAt_id.pow 2)
  have hh := chart_trace (g := growth) (p := intake) (e := 1) (d := 1)
    (Q := 5/6) (r := 5/6) (s := 1/2) (by norm_num) (by norm_num) (by norm_num [growth])
    (by norm_num [growth]) (by norm_num [D,E,(growth_deriv _).deriv,growth]) hc
    (Filter.Eventually.of_forall (fun t => (growth_deriv t).differentiableAt)) (growth_deriv₂ _).differentiableAt
    intake_deriv_at_ratio.differentiableAt (by norm_num [intake]) (by norm_num [intake])
  rw [exact_enrichment.1, exact_enrichment.2.2] at hh
  exact hh


/-- The affine growth factor in the original weak-Allee P4 application of Theorem 1. -/
theorem weak_allee_P4 {r α e d s : ℝ} (hr : 0 < r) (hα : 0 < α)
    (he : 0 < e) (hd : 0 < d) (hs : 0 < s) :
    PhysicalTraceFalls (fun x => r*(1+α*x)) e d s := by
  let g : ℝ → ℝ := fun x => r*(1+α*x)
  have reg : ContDiff ℝ 2 g := contDiff_const.mul (contDiff_const.add (contDiff_const.mul contDiff_id))
  have gd (x : ℝ) : HasDerivAt g (r*α) x := by
    simpa [g, id] using (((hasDerivAt_const x (1:ℝ)).add ((hasDerivAt_id x).const_mul α)).const_mul r)
  have gg : deriv g = (fun _ => r*α) := funext fun x => (gd x).deriv
  have gpos {x : ℝ} (hx : 0 < x) : 0 < g x := by dsimp [g]; positivity
  apply (physical_criterion (I := Set.Ioi (0:ℝ)) isOpen_Ioi (fun _ hn => hn)
    hs he hd reg.contDiffOn (fun _ hx => gpos hx) (fun x _ => (gd x).deriv ▸ mul_pos hr hα)).mpr
  have second : HasDerivAt (deriv g) 0 s := by rw [gg]; exact hasDerivAt_const s _
  rw [D1Core.reciprocal_curvature (gpos hs).ne' (Filter.Eventually.of_forall (fun x => (gd x).differentiableAt))
    second.differentiableAt, (gd s).deriv, second.deriv]
  unfold D1Core.curvature
  simp only [mul_zero, sub_zero]
  exact div_nonneg (by positivity) (pow_nonneg (gpos hs).le _)

#print axioms weak_allee_P4

#print axioms exact_physical_trace
#print axioms exact_equilibrium
#print axioms exact_matrix
#print axioms exact_trace_det
#print axioms exact_curvature
#print axioms exact_enrichment

end
end D1Example
