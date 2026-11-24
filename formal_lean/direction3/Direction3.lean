import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Structural results for the seven-parameter field in Direction 3, Methods (1)–(2). -/
noncomputable section
open Set
namespace Direction3

structure Params where
  r : ℝ
  K : ℝ
  alpha : ℝ
  m : ℝ
  beta : ℝ
  e : ℝ
  d : ℝ

structure Positive (p : Params) : Prop where
  r : 0 < p.r
  K : 0 < p.K
  alpha : 0 < p.alpha
  m : 0 < p.m
  beta : 0 < p.beta
  e : 0 < p.e
  d : 0 < p.d

def growthRate (p : Params) (x : ℝ) : ℝ := p.r * (1 - x / p.K) * (1 + p.alpha * x)
def growth (p : Params) (x : ℝ) : ℝ := x * growthRate p x
def flux (p : Params) (x y : ℝ) : ℝ := p.m * x * y / (p.beta + y)
def target (p : Params) (x y : ℝ) : ℝ := growth p x - flux p x y
def consumer (p : Params) (x y : ℝ) : ℝ := p.e * flux p x y - p.d * y
def consumerRate (p : Params) (x y : ℝ) : ℝ := p.e * p.m * x / (p.beta + y) - p.d

theorem denominators {p : Params} (hp : Positive p) {y : ℝ} (hy : 0 ≤ y) :
    p.K ≠ 0 ∧ p.beta + y ≠ 0 :=
  ⟨hp.K.ne', (add_pos_of_pos_of_nonneg hp.beta hy).ne'⟩

theorem field_eq (p : Params) (x y : ℝ) :
    target p x y = p.r*x*(1-x/p.K)*(1+p.alpha*x) - p.m*x*y/(p.beta+y) ∧
    consumer p x y = p.e*p.m*x*y/(p.beta+y)-p.d*y := by
  constructor <;> simp only [target, consumer, growth, growthRate, flux, div_eq_mul_inv] <;> ring

theorem consumer_factors (p : Params) (x y : ℝ) :
    consumer p x y = consumerRate p x y * y := by
  unfold consumer consumerRate flux
  ring

theorem target_factors (p : Params) (x y : ℝ) :
    target p x y = (growthRate p x - p.m*y/(p.beta+y)) * x := by
  unfold target growth flux
  ring

@[simp] theorem flux_zero (p : Params) (x : ℝ) : flux p x 0 = 0 := by simp [flux]
@[simp] theorem target_axis (p : Params) (x : ℝ) : target p x 0 = growth p x := by simp [target]
@[simp] theorem consumer_axis (p : Params) (x : ℝ) : consumer p x 0 = 0 := by simp [consumer]

/-- A finite forward solution is continuous up to both ends and satisfies the ODE
with a right derivative at every point before the final time. -/
structure Solution (p : Params) (x y : ℝ → ℝ) (a b : ℝ) : Prop where
  cx : ContinuousOn x (Icc a b)
  cy : ContinuousOn y (Icc a b)
  dx : ∀ t ∈ Ico a b, HasDerivWithinAt x (target p (x t) (y t)) (Ici t) t
  dy : ∀ t ∈ Ico a b, HasDerivWithinAt y (consumer p (x t) (y t)) (Ici t) t

private theorem linear_zero {u rate : ℝ → ℝ} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hc : ContinuousOn rate (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt u (rate t * u t) (Ici t) t) (h0 : u a = 0) :
    ∀ t ∈ Icc a b, u t = 0 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc.norm
  have bound : ∀ t ∈ Ico a b, ‖rate t * u t‖ ≤ M * ‖u t‖ + 0 := by
    intro t ht
    have hMt : ‖rate t‖ ≤ M := hM ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩
    rw [norm_mul, add_zero]
    exact mul_le_mul_of_nonneg_right hMt (norm_nonneg _)
  have zeroBound := norm_le_gronwallBound_of_norm_deriv_right_le hu hd
    (δ := 0) (by simp [h0]) bound
  intro t ht
  exact norm_le_zero_iff.mp (by simpa only [gronwallBound_ε0_δ0] using zeroBound t ht)

private theorem linear_nonnegative {u rate : ℝ → ℝ} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hc : ContinuousOn rate (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt u (rate t * u t) (Ici t) t) (h0 : 0 ≤ u a) :
    ∀ t ∈ Icc a b, 0 ≤ u t := by
  intro t ht
  by_contra! hn
  obtain ⟨z, hz, huz⟩ := intermediate_value_Icc' ht.1 (hu.mono (Icc_subset_Icc_right ht.2))
    (show 0 ∈ Icc (u t) (u a) from ⟨hn.le, h0⟩)
  have subset := Icc_subset_Icc hz.1 ht.2
  have zero := linear_zero (hu.mono subset) (hc.mono subset)
    (fun w hw => hd w (Ico_subset_Ico hz.1 ht.2 hw)) huz t ⟨hz.2, le_rfl⟩
  exact hn.ne zero

private theorem rate_continuous {p : Params} {x y : ℝ → ℝ} {a b : ℝ}
    (sol : Solution p x y a b) (regular : ∀ t ∈ Icc a b, p.beta + y t ≠ 0) :
    ContinuousOn (fun t => consumerRate p (x t) (y t)) (Icc a b) :=
  (((continuousOn_const.mul sol.cx).div (continuousOn_const.add sol.cy) regular).sub
    continuousOn_const : ContinuousOn (fun t => (p.e*p.m)*x t/(p.beta+y t)-p.d) _)

/-- Uniqueness of the zero consumer coordinate on every compact regular
solution interval. The solution need not be assumed nonnegative. -/
theorem axis_invariant {p : Params} {x y : ℝ → ℝ} {a b : ℝ}
    (sol : Solution p x y a b) (h0 : y a = 0)
    (regular : ∀ t ∈ Icc a b, p.beta + y t ≠ 0) : ∀ t ∈ Icc a b, y t = 0 :=
  linear_zero sol.cy (rate_continuous sol regular)
    (fun t ht => (sol.dy t ht).congr_deriv (consumer_factors p _ _)) h0

/-- Nonnegative initial populations stay nonnegative on a regular solution interval. -/
theorem nonnegative_quadrant {p : Params} {x y : ℝ → ℝ} {a b : ℝ}
    (sol : Solution p x y a b) (hx0 : 0 ≤ x a) (hy0 : 0 ≤ y a)
    (regular : ∀ t ∈ Icc a b, p.beta + y t ≠ 0) :
    ∀ t ∈ Icc a b, 0 ≤ x t ∧ 0 ≤ y t := by
  have cg : ContinuousOn (fun t => growthRate p (x t)) (Icc a b) :=
    (continuousOn_const.mul (continuousOn_const.sub (sol.cx.div_const p.K))).mul
      (continuousOn_const.add (continuousOn_const.mul sol.cx))
  have ct : ContinuousOn (fun t => growthRate p (x t) - p.m*y t/(p.beta+y t)) (Icc a b) :=
    cg.sub ((continuousOn_const.mul sol.cy).div (continuousOn_const.add sol.cy) regular)
  have nx := linear_nonnegative sol.cx ct
    (fun t ht => (sol.dx t ht).congr_deriv (target_factors p _ _)) hx0
  have ny := linear_nonnegative sol.cy (rate_continuous sol regular)
    (fun t ht => (sol.dy t ht).congr_deriv (consumer_factors p _ _)) hy0
  exact fun t ht => ⟨nx t ht, ny t ht⟩

structure Run where
  params : Params
  target0 : ℝ
  consumer0 : ℝ

def ablate (run : Run) : Run := { run with consumer0 := 0 }

theorem ablation_inputs (run : Run) :
    (ablate run).params = run.params ∧ (ablate run).target0 = run.target0 ∧
      (ablate run).consumer0 = 0 := ⟨rfl, rfl, rfl⟩

def Runs (run : Run) (x y : ℝ → ℝ) (a b : ℝ) : Prop :=
  Solution run.params x y a b ∧ x a = run.target0 ∧ y a = run.consumer0

/-- The counterfactual holds the fitted coefficients and initial target fixed.
It solves the scalar target equation on its entire regular forecast interval. -/
theorem ablation_trajectory {run : Run} {x y : ℝ → ℝ} {a b : ℝ}
    (runOK : Runs (ablate run) x y a b)
    (regular : ∀ t ∈ Icc a b, run.params.beta + y t ≠ 0) :
    x a = run.target0 ∧
    (∀ t ∈ Icc a b, y t = 0 ∧ flux run.params (x t) (y t) = 0) ∧
    (∀ t ∈ Ico a b, HasDerivWithinAt x (growth run.params (x t)) (Ici t) t) := by
  have hs : Solution run.params x y a b := runOK.1
  have hz := axis_invariant hs (show y a = 0 from runOK.2.2) regular
  refine ⟨runOK.2.1, ?_, ?_⟩
  · intro t ht
    exact ⟨hz t ht, by simp [hz t ht]⟩
  · intro t ht
    simpa only [hz t ⟨ht.1, ht.2.le⟩, target_axis] using hs.dx t ht

/-- A solution of the scalar target equation lifts to an actual solution of
the two coupled equations with identically zero consumer. -/
theorem lift_scalar {p : Params} {x : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn x (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt x (growth p (x t)) (Ici t) t) :
    Solution p x (fun _ => 0) a b := by
  refine ⟨hc, continuousOn_const, ?_, ?_⟩
  · intro t ht
    simpa only [target_axis] using hd t ht
  · intro t _
    simpa only [consumer_axis] using
      (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt (s := Ici t)

/-- Instantaneous sign conditions in Supplementary Note 1. -/
theorem opposed_rates {p : Params} {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (target p x y < 0 ∧ 0 < consumer p x y) ↔
    (growthRate p x < p.m*y/(p.beta+y) ∧ p.d < p.e*p.m*x/(p.beta+y)) := by
  have hxform : target p x y = x * (growthRate p x - p.m*y/(p.beta+y)) := by
    unfold target growth flux
    ring
  rw [hxform, consumer_factors]
  simp [consumerRate, mul_neg_iff, hx, not_lt_of_ge hx.le, sub_neg, mul_pos_iff_of_pos_right hy,
    sub_pos]

/-- Pointwise ingredient of the sufficient exponential consumer-decline bound. -/
theorem consumer_rate_upper {p : Params} (hp : Positive p) {x y M : ℝ}
    (hx : 0 ≤ x) (hxM : x ≤ M) (hy : 0 ≤ y) :
    consumerRate p x y ≤ -(p.d - p.e*p.m*M/p.beta) := by
  have hem := mul_nonneg hp.e.le hp.m.le
  have den := add_pos_of_pos_of_nonneg hp.beta hy
  have h1 : p.e*p.m*x/(p.beta+y) ≤ p.e*p.m*M/(p.beta+y) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxM hem) den.le
  have h2 : p.e*p.m*M/(p.beta+y) ≤ p.e*p.m*M/p.beta :=
    div_le_div_of_nonneg_left (mul_nonneg hem (hx.trans hxM)) hp.beta (by linarith)
  unfold consumerRate
  linarith

/-- The exponential envelope in Supplementary Note 1, conditional on the stated
population bounds. A positive decay rate makes this an exponential decline bound. -/
theorem consumer_envelope {p : Params} (hp : Positive p) {x y : ℝ → ℝ} {a b M : ℝ}
    (s : Solution p x y a b)
    (bounds : ∀ t ∈ Ico a b, 0 ≤ x t ∧ x t ≤ M ∧ 0 ≤ y t) :
    ∀ t ∈ Icc a b, y t ≤ y a * Real.exp (-(p.d - p.e*p.m*M/p.beta) * (t-a)) := by
  let k := -(p.d - p.e*p.m*M/p.beta)
  have bound : ∀ t ∈ Ico a b, consumer p (x t) (y t) ≤ k * y t + 0 := by
    intro t ht
    obtain ⟨hx, hxM, hy⟩ := bounds t ht
    rw [add_zero, consumer_factors]
    exact mul_le_mul_of_nonneg_right (consumer_rate_upper hp hx hxM hy) hy
  have env := le_gronwallBound_of_liminf_deriv_right_le s.cy
    (fun t ht _ hr => (s.dy t ht).liminf_right_slope_le hr) (le_refl (y a)) bound
  intro t ht
  simpa only [gronwallBound_ε0] using env t ht

/-- A positive constant change of consumer units in Methods and Supplementary Note 3. -/
def scaleConsumer (p : Params) (f : ℝ) : Params := { p with beta := f*p.beta, e := f*p.e }

theorem scaling_field {p : Params} {f : ℝ} (hf : 0 < f) (x y : ℝ)
    (hd : p.beta + y ≠ 0) :
    target (scaleConsumer p f) x (f*y) = target p x y ∧
    consumer (scaleConsumer p f) x (f*y) = f * consumer p x y := by
  have hflux : flux (scaleConsumer p f) x (f*y) = flux p x y := by
    change p.m*x*(f*y)/(f*p.beta+f*y) = p.m*x*y/(p.beta+y)
    rw [← mul_add]
    field_simp [hf.ne', hd]
    ring
  constructor
  · unfold target
    rw [hflux]
    rfl
  · unfold consumer
    rw [hflux]
    change f * p.e * flux p x y - p.d*(f*y) = f * (p.e * flux p x y - p.d*y)
    ring

theorem scaling_solution {p : Params} {f : ℝ} (hf : 0 < f) {x y : ℝ → ℝ} {a b : ℝ}
    (s : Solution p x y a b) (regular : ∀ t ∈ Ico a b, p.beta + y t ≠ 0) :
    Solution (scaleConsumer p f) x (fun t => f * y t) a b := by
  refine ⟨s.cx, continuousOn_const.mul s.cy, ?_, ?_⟩
  · intro t ht
    rw [(scaling_field hf (x t) (y t) (regular t ht)).1]
    exact s.dx t ht
  · intro t ht
    rw [(scaling_field hf (x t) (y t) (regular t ht)).2]
    exact (s.dy t ht).const_mul f

/-- The RMSE of a nonempty finite forecast, represented in Euclidean coordinates.
The denominator uses n+1 to make the positive sample count explicit. -/
def rmse {n : ℕ} (u v : EuclideanSpace ℝ (Fin (n+1))) : ℝ :=
  dist u v / Real.sqrt (n+1 : ℕ)

theorem rmse_eq_sum {n : ℕ} (u v : EuclideanSpace ℝ (Fin (n+1))) :
    rmse u v = Real.sqrt ((∑ i, (u i - v i)^2) / (n+1 : ℕ)) := by
  rw [rmse, EuclideanSpace.dist_eq, Real.sqrt_div' _ (show 0 ≤ ((n+1 : ℕ) : ℝ) by positivity)]
  simp only [Real.dist_eq, sq_abs]

/-- Supplementary Note 1: a change in held RMSE is bounded by displacement
on the same finite grid. No numerical forecasts enter the statement. -/
theorem rmse_displacement {n : ℕ} (u v obs : EuclideanSpace ℝ (Fin (n+1))) :
    |rmse u obs - rmse v obs| ≤ rmse u v := by
  have h : |dist u obs - dist v obs| ≤ dist u v := by
    apply abs_le.mpr
    have hu := dist_triangle u v obs
    have hv := dist_triangle v u obs
    rw [dist_comm v u] at hv
    exact ⟨by linarith, by linarith⟩
  unfold rmse
  rw [← sub_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)

/-- If the displacement is strictly smaller than the original margin to a
comparator, the two errors lie on the same side of its error. -/
theorem rmse_strict_ranking {n : ℕ} (u v obs : EuclideanSpace ℝ (Fin (n+1)))
    {comparator : ℝ} (gap : rmse u v < |rmse u obs - comparator|) :
    (rmse u obs < comparator ↔ rmse v obs < comparator) ∧
    (comparator < rmse u obs ↔ comparator < rmse v obs) := by
  have h := abs_le.mp (rmse_displacement u v obs)
  have hn : 0 ≤ rmse u v := div_nonneg dist_nonneg (Real.sqrt_nonneg _)
  rcases le_total (rmse u obs) comparator with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at gap
    constructor <;> constructor <;> intro <;> linarith [h.1, h.2]
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at gap
    constructor <;> constructor <;> intro <;> linarith [h.1, h.2]

/-- The two measured CD3 values are exact integers in tenths of a reported count. -/
structure Observation where
  genotype : String
  ratioDenominator : ℕ
  day3 : ℕ
  day6 : ℕ

def observations : List Observation := [
  ⟨"KO", 16, 46200, 85368⟩,
  ⟨"KO", 24, 12886, 31088⟩,
  ⟨"KO", 30, 3981, 22313⟩,
  ⟨"KO", 40, 3248, 13037⟩,
  ⟨"KO", 50, 1257, 7020⟩,
  ⟨"KO", 60, 1257, 5140⟩,
  ⟨"WT", 16, 36876, 134632⟩,
  ⟨"WT", 24, 16867, 66063⟩,
  ⟨"WT", 30, 11210, 32342⟩,
  ⟨"WT", 40, 8695, 29459⟩,
  ⟨"WT", 50, 1990, 7521⟩,
  ⟨"WT", 60, 2514, 7145⟩]

/-- Each prespecified genotype-ratio pair appears once in the encoded source extract. -/
theorem observed_keys :
    observations.map (fun row => (row.genotype, row.ratioDenominator)) =
    ["KO", "WT"].flatMap (fun g => [16,24,30,40,50,60].map (fun k => (g, k))) := by decide

/-- On the twelve encoded pairs, all measured day-6 values exceed day-3 values. -/
theorem observed_early_rises : observations.length = 12 ∧
    (observations.filter (fun row => decide (row.day3 < row.day6))).length = 12 := by decide

end Direction3

#print axioms Direction3.denominators
#print axioms Direction3.field_eq
#print axioms Direction3.consumer_factors
#print axioms Direction3.target_factors
#print axioms Direction3.flux_zero
#print axioms Direction3.target_axis
#print axioms Direction3.consumer_axis
#print axioms Direction3.axis_invariant
#print axioms Direction3.nonnegative_quadrant
#print axioms Direction3.ablation_inputs
#print axioms Direction3.ablation_trajectory
#print axioms Direction3.lift_scalar
#print axioms Direction3.opposed_rates
#print axioms Direction3.consumer_rate_upper
#print axioms Direction3.consumer_envelope
#print axioms Direction3.scaling_field
#print axioms Direction3.scaling_solution
#print axioms Direction3.rmse_eq_sum
#print axioms Direction3.rmse_displacement
#print axioms Direction3.rmse_strict_ranking
#print axioms Direction3.observed_keys
#print axioms Direction3.observed_early_rises
