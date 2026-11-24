import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Filter Topology

namespace D1Core
noncomputable section

/-- At density s, a = g(s), b = g'(s), c = g''(s). -/
def upper (s a b : ℝ) := a / (1 + s * b / a)
def elasticityPrime (s a b c : ℝ) := b / a + s * c / a - s * b^2 / a^2
def curvature (a b c : ℝ) := (2*b^2 - a*c) / a^3

theorem reciprocal_first {g : ℝ → ℝ} {s : ℝ}
    (h : DifferentiableAt ℝ g s) (ha : g s ≠ 0) :
    deriv (fun t => (g t)⁻¹) s = -deriv g s / (g s)^2 :=
  (h.hasDerivAt.inv ha).deriv

theorem reciprocal_curvature {g : ℝ → ℝ} {s : ℝ}
    (ha : g s ≠ 0) (hg : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t)
    (hgg : DifferentiableAt ℝ (deriv g) s) :
    deriv (deriv (fun t => (g t)⁻¹)) s = curvature (g s) (deriv g s) (deriv (deriv g) s) := by
  have h := hg.self_of_nhds.hasDerivAt
  have hval : ∀ᶠ t in 𝓝 s, g t ≠ 0 := h.continuousAt.eventually_ne ha
  have heq : deriv (fun t => (g t)⁻¹) =ᶠ[𝓝 s] (fun t => -deriv g t / (g t)^2) := by
    filter_upwards [hg,hval] with t hd hn using reciprocal_first hd hn
  have hquot := (hgg.hasDerivAt.neg.div (h.pow 2) (pow_ne_zero _ ha)).congr_of_eventuallyEq heq
  rw [hquot.deriv]
  unfold curvature
  field_simp
  <;> ring

theorem upper_pos {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) :
    0 < upper s a b := by unfold upper; positivity

theorem endpoint {s a b c : ℝ} (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) :
    upper s a b * elasticityPrime s a b c - b =
    -(s*a^2/(1+s*b/a)) * curvature a b c := by
  have hsum : 0 < 1+s*b/a := by positivity
  unfold upper elasticityPrime curvature
  field_simp [ne_of_gt ha, ne_of_gt hsum] <;> ring

/-- Three strictly interior loads, with negative, zero and positive slopes. -/
theorem all_signs (s a b c : ℝ) (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (hcurv : curvature a b c < 0) :
    ∃ q₁ q₂ q₃ : ℝ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < q₃ ∧ q₃ < upper s a b ∧
      q₁ * elasticityPrime s a b c - b < 0 ∧ q₂ * elasticityPrime s a b c - b = 0 ∧
      0 < q₃ * elasticityPrime s a b c - b := by
  let U := upper s a b
  let v := elasticityPrime s a b c
  have hu : 0 < U := upper_pos hs ha hb
  have hfactor : 0 < s*a^2/(1+s*b/a) := by positivity
  have htop : 0 < U*v-b := by
    change 0 < upper s a b * elasticityPrime s a b c - b
    rw [endpoint hs ha hb]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hfactor) hcurv
  have hv : 0 < v := by
    by_contra! hn
    have := mul_nonpos_of_nonneg_of_nonpos hu.le hn
    linarith
  let mid := b/v
  have hm : 0 < mid := div_pos hb hv
  have hmU : mid < U := (div_lt_iff₀ hv).2 (by linarith)
  have hmval : mid*v = b := div_mul_cancel₀ b hv.ne'
  refine ⟨mid/2, mid, (mid+U)/2, by linarith, by linarith, by linarith,
    by linarith, ?_, ?_, ?_⟩
  · change mid/2*v-b < 0
    linarith only [hmval, hb]
  · change mid*v-b = 0
    linarith
  · change 0 < (mid+U)/2*v-b
    linarith only [hmval,htop]

theorem criterion (s a b c : ℝ) (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) :
    (∀ Q : ℝ, 0 < Q → Q < upper s a b → Q * elasticityPrime s a b c - b < 0) ↔
    0 ≤ curvature a b c := by
  constructor
  · intro hall
    by_contra! hc
    obtain ⟨l,m,q,hl,hlm,hmq,hq,_,_,hpos⟩ := all_signs s a b c hs ha hb hc
    exact (not_lt_of_ge hpos.le) (hall q (hl.trans (hlm.trans hmq)) hq)
  · intro hc q hq hqu
    have hfac : 0 < s*a^2/(1+s*b/a) := by positivity
    have he := endpoint (c := c) hs ha hb
    have hend := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hfac.le) hc
    by_cases hv : 0 < elasticityPrime s a b c
    · linarith only [he,hend,mul_lt_mul_of_pos_right hqu hv]
    · have := mul_nonpos_of_nonneg_of_nonpos hq.le (le_of_not_gt hv)
      linarith

#print axioms reciprocal_first
#print axioms reciprocal_curvature
#print axioms endpoint
#print axioms all_signs
#print axioms criterion

end
end D1Core
