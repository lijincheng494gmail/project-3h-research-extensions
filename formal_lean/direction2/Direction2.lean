import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Equilibrium comparisons with shared predator parameters. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Direction2

structure Params where
  m : ℝ
  β : ℝ
  e : ℝ
  d : ℝ
  hm : 0 < m
  hβ : 0 < β
  he : 0 < e
  hd : 0 < d

namespace Params
variable (p : Params)

def intake (y : ℝ) := p.m * y / (p.β + y)
def chart (h y : ℝ) := (p.β + y) * (p.d + h*y) / (p.e*p.m)
def preyRHS (g : ℝ → ℝ) (x y : ℝ) := x*(g x - p.intake y)
def predatorRHS (h x y : ℝ) := y*(p.e*p.m*x/(p.β+y)-p.d) - h*y^2

/-- At positive coordinates these are the two cleared equilibrium equations. -/
def Root (g : ℝ → ℝ) (h x y : ℝ) : Prop :=
  g x * (p.β+y) = p.m*y ∧ p.e*p.m*x = (p.β+y)*(p.d+h*y)

theorem root_iff (g : ℝ → ℝ) {h x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    p.Root g h x y ↔ p.preyRHS g x y = 0 ∧ p.predatorRHS h x y = 0 := by
  have nb := (add_pos p.hβ hy).ne'
  unfold Root preyRHS predatorRHS intake
  constructor
  · rintro ⟨hg, hp⟩
    constructor
    · rw [← (eq_div_iff nb).2 hg]; ring
    · rw [(div_eq_iff nb).2 (show p.e*p.m*x = (p.d+h*y)*(p.β+y) by linarith [hp])]
      ring
  · rintro ⟨hg,hp⟩
    have hg' := (mul_eq_zero.mp hg).resolve_left hx.ne'
    refine ⟨(eq_div_iff nb).1 (sub_eq_zero.mp hg'), ?_⟩
    have hp' : y*(p.e*p.m*x/(p.β+y) - (p.d+h*y)) = 0 := by linarith [hp]
    have u := (div_eq_iff nb).1 (sub_eq_zero.mp ((mul_eq_zero.mp hp').resolve_left hy.ne'))
    linarith

theorem intake_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : p.intake a < p.intake b := by
  unfold intake
  apply (div_lt_div_iff₀ (add_pos_of_pos_of_nonneg p.hβ ha)
    (add_pos p.hβ (lt_of_le_of_lt ha hab))).2
  nlinarith only [mul_pos p.hm (mul_pos p.hβ (sub_pos.mpr hab))]

theorem chart_lt_y {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a) (hab : a < b) :
    p.chart h a < p.chart h b := by
  unfold chart
  apply div_lt_div_of_pos_right _ (mul_pos p.he p.hm)
  apply (mul_lt_mul_of_pos_right (add_lt_add_left hab _) (add_pos_of_pos_of_nonneg p.hd (mul_nonneg hh ha))).trans_le
  exact mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left hab.le hh) _) (add_nonneg p.hβ.le (ha.trans hab.le))

theorem chart_le_h {r h y : ℝ} (hrh : r ≤ h) (hy : 0 ≤ y) : p.chart r y ≤ p.chart h y := by
  unfold chart
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_right hrh hy) _)
    (add_nonneg p.hβ.le hy)) (mul_pos p.he p.hm).le

theorem Root.coords {g : ℝ → ℝ} {h x y : ℝ} (a : p.Root g h x y) (hy : 0 < y) :
    g x = p.intake y ∧ x = p.chart h y :=
  ⟨(eq_div_iff (add_pos p.hβ hy).ne').2 a.1,
    (eq_div_iff (mul_pos p.he p.hm).ne').2 (by linarith [a.2])⟩

/-- The determinant in cleared nullcline coordinates. Its positive factor is
    related to the original-time Jacobian determinant in determinant_eq. -/
def scaledDet (g : ℝ → ℝ) (h x y : ℝ) :=
  p.e*p.m*(p.m-g x) - (p.d+h*(p.β+2*y))*(p.β+y)*deriv g x

def detJ (g : ℝ → ℝ) (h x y : ℝ) :=
  (x * deriv g x) * (-(y*(p.e*p.m*x/(p.β+y)^2+h))) -
    (-(p.m*x*p.β/(p.β+y)^2))*(p.e*p.m*y/(p.β+y))

theorem determinant_eq {g : ℝ → ℝ} {h x y : ℝ} (r : p.Root g h x y) (hy : 0 < y) :
    p.detJ g h x y = x*y/(p.β+y)^2 * p.scaledDet g h x y := by
  obtain ⟨hg,hp⟩ := r
  have nb := (add_pos p.hβ hy).ne'
  unfold detJ scaledDet
  rw [(eq_div_iff nb).2 hg, hp]
  field_simp [nb]
  ring

structure Branch (g : ℝ → ℝ) (H : ℝ) where
  x : ℝ → ℝ
  y : ℝ → ℝ
  cx : ContinuousOn x (Icc 0 H)
  cy : ContinuousOn y (Icc 0 H)
  posX : ∀ t ∈ Icc 0 H, 0 < x t
  posY : ∀ t ∈ Icc 0 H, 0 < y t
  root : ∀ t ∈ Icc 0 H, p.Root g t (x t) (y t)
  regular : ∀ t ∈ Icc 0 H, 0 < p.detJ g t (x t) (y t)
  smooth : ∀ t ∈ Icc 0 H, DifferentiableAt ℝ g (x t)

/-- A continuous positive-determinant graph already has the required
    sensitivities.  A secant proof avoids assuming differentiated
    equilibrium equations or postulating the implicit-function theorem. -/
theorem branch_derivatives {g : ℝ → ℝ} {H t : ℝ} (b : p.Branch g H)
    (ht : t ∈ Icc 0 H) :
    let x := b.x t; let y := b.y t
    let D := p.scaledDet g t x y
    HasDerivWithinAt b.x ((p.m-g x)*((p.β+y)*y)/D) (Icc 0 H) t ∧
    HasDerivWithinAt b.y ((deriv g x*(p.β+y))*((p.β+y)*y)/D) (Icc 0 H) t := by
  let S := Icc 0 H
  let x := b.x t
  let y := b.y t
  let u := fun z => dslope g x (b.x z)*(p.β+b.y z)
  let v := p.m-g x
  let V := fun z => p.d+z*(p.β+b.y z+y)
  let W := (p.β+y)*y
  let D := fun z => p.e*p.m*v - V z * u z
  have du : u t = deriv g x * (p.β+y) := by simp [u,x,y]
  have d0 : D t = p.scaledDet g t x y := by
    simp only [D,du,scaledDet,V,v]; dsimp [y]; ring
  have pos := b.regular t ht
  rw [p.determinant_eq (b.root t ht) (b.posY t ht)] at pos
  have hD : 0 < D t := by
    rw [d0]
    exact pos_of_mul_pos_right pos (div_nonneg (mul_nonneg (b.posX t ht).le
      (b.posY t ht).le) (sq_nonneg _))
  have hx := b.cx t ht
  have hy := b.cy t ht
  have hu : ContinuousWithinAt u S t :=
    ((continuousAt_dslope_same.mpr (b.smooth t ht)).comp_continuousWithinAt hx).mul
      (continuousWithinAt_const.add hy)
  have hV : ContinuousWithinAt V S t := continuousWithinAt_const.add
    (continuousWithinAt_id.mul ((continuousWithinAt_const.add hy).add continuousWithinAt_const))
  have hc : ContinuousWithinAt D S t := continuousWithinAt_const.sub (hV.mul hu)
  let A := S \ {t}
  have subS : A ⊆ S := diff_subset
  have hn : ∀ᶠ z in 𝓝[A] t, D z ≠ 0 :=
    (hc.mono subS).tendsto.eventually (eventually_ne_nhds hD.ne')
  have eqs : ∀ᶠ z in 𝓝[A] t,
      slope b.x t z = v*W/D z ∧ slope b.y t z = u z*W/D z := by
    filter_upwards [self_mem_nhdsWithin, hn] with z hz nz
    have hs : z ∈ S := hz.1
    have nt : z ≠ t := hz.2
    obtain ⟨ge,pe⟩ := b.root z hs
    obtain ⟨g0,p0⟩ := b.root t ht
    have sec := sub_smul_dslope g x (b.x z)
    rw [smul_eq_mul] at sec
    have E1 : u z*(b.x z-x) = v*(b.y z-y) := by
      dsimp [u,v,x,y] at sec ⊢
      linear_combination (p.β+b.y z)*sec + ge - g0
    have E2 : p.e*p.m*(b.x z-x) = V z*(b.y z-y)+(z-t)*W := by
      dsimp [V,W,x,y]
      linear_combination pe - p0
    simp only [slope_def_field]
    constructor
    · apply (div_eq_div_iff (sub_ne_zero.mpr nt) nz).2
      change (b.x z-x)*(p.e*p.m*v - V z*u z) = _
      linear_combination v*E2 - V z*E1
    · apply (div_eq_div_iff (sub_ne_zero.mpr nt) nz).2
      change (b.y z-y)*(p.e*p.m*v - V z*u z) = _
      linear_combination u z*E2 - (p.e*p.m)*E1
  constructor
  · apply hasDerivWithinAt_iff_tendsto_slope.mpr
    rw [← d0]
    exact ((tendsto_const_nhds.div (hc.mono subS).tendsto hD.ne').congr'
      (eqs.mono fun _ hz => hz.1.symm))
  · apply hasDerivWithinAt_iff_tendsto_slope.mpr
    rw [← d0, ← du]
    exact ((((hu.mono subS).tendsto.mul tendsto_const_nhds).div
      (hc.mono subS).tendsto hD.ne').congr' (eqs.mono fun _ hz => hz.2.symm))

theorem prey_strictMono {g : ℝ → ℝ} {H : ℝ} (b : p.Branch g H) :
    StrictMonoOn b.x (Icc 0 H) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 H) b.cx
  intro t ht
  have ht' := interior_subset ht
  have hy := b.posY t ht'
  have hg := (Params.Root.coords p (b.root t ht') hy).1
  have rlt : g (b.x t) < p.m := by
    rw [hg,intake]
    exact (div_lt_iff₀ (add_pos p.hβ hy)).2 (by nlinarith [mul_pos p.hm p.hβ])
  have hp := b.regular t ht'
  rw [p.determinant_eq (b.root t ht') hy] at hp
  have hdet := pos_of_mul_pos_right hp (div_nonneg (mul_nonneg (b.posX t ht').le hy.le) (sq_nonneg _))
  rw [((p.branch_derivatives b ht').1.hasDerivAt (mem_interior_iff_mem_nhds.mp ht)).deriv]
  exact div_pos (mul_pos (sub_pos.mpr rlt) (mul_pos (add_pos p.hβ hy) hy)) hdet

/-- Finite arbitrary-growth ordering. The gap is needed only at the prey
    coordinates of the upper branch, once they are strictly right of the start. -/
theorem finite_order {g₁ g₂ : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (L : p.Branch g₁ H) (U : p.Branch g₂ H)
    (startX : L.x 0 = U.x 0) (_startY : L.y 0 = U.y 0)
    (gap : ∀ z ∈ Ioc 0 H, U.x 0 < U.x z → g₁ (U.x z) < g₂ (U.x z)) :
    ∀ h ∈ Ioc 0 H, L.x h < U.x h ∧ L.y h < U.y h := by
  intro h hh
  have hh' : h ∈ Icc 0 H := ⟨hh.1.le,hh.2⟩
  have h0 : (0:ℝ) ∈ Icc 0 H := ⟨le_rfl,hH.le⟩
  have hx := p.prey_strictMono U h0 hh' hh.1
  have hg := gap h hh hx
  have hu := Params.Root.coords p (U.root h hh') (U.posY h hh')
  have orderX : L.x h < U.x h := by
    apply lt_of_not_ge
    intro rev
    have hc : ContinuousOn L.x (Icc 0 h) := L.cx.mono (Icc_subset_Icc_right hh.2)
    obtain ⟨t,ht,hit⟩ := intermediate_value_Icc hh.1.le hc
      (show U.x h ∈ Icc (L.x 0) (L.x h) from ⟨startX ▸ hx.le,rev⟩)
    have ht' : t ∈ Icc 0 H := ⟨ht.1,ht.2.trans hh.2⟩
    have hl := Params.Root.coords p (L.root t ht') (L.posY t ht')
    have orderY : L.y t < U.y h := by
      by_contra! he
      have le : p.intake (U.y h) ≤ p.intake (L.y t) := by
        rcases he.eq_or_lt with e | e
        · rw [e]
        · exact (p.intake_lt (U.posY h hh').le e).le
      rw [← hu.1, ← hl.1, hit] at le
      exact (not_le_of_gt hg) le
    have val := (p.chart_le_h ht.2 (L.posY t ht').le).trans_lt
      (p.chart_lt_y hh.1.le (L.posY t ht').le orderY)
    rw [← hl.2, ← hu.2, hit] at val
    exact (lt_irrefl _) val
  refine ⟨orderX, ?_⟩
  apply lt_of_not_ge
  intro rev
  have hl := Params.Root.coords p (L.root h hh') (L.posY h hh')
  rcases rev.eq_or_lt with e | e
  · rw [hl.2,hu.2,e] at orderX; exact (lt_irrefl _) orderX
  · have contra := p.chart_lt_y hh.1.le (U.posY h hh').le e
    rw [← hu.2, ← hl.2] at contra
    exact (not_lt_of_ge orderX.le) contra

end Params

structure Calibration (p : Params) where
  K : ℝ
  A : ℝ
  α : ℝ
  x₀ : ℝ
  y₀ : ℝ
  posA : 0 < A
  left : A < x₀
  right : x₀ < K
  alpha_pos : 0 < α
  weak_allee : 1 < α*K
  posY : 0 < y₀
  compatible : p.e*p.m*x₀ = p.d*(p.β+y₀)

namespace Calibration
variable {p : Params} (c : Calibration p)

def growth (s x : ℝ) : ℝ :=
  p.intake c.y₀ * ((c.K-x)/(c.K-c.x₀)) * (1+s*(x-c.x₀))

def weakS := c.α/(1+c.α*c.x₀)
def strongS := 1/(c.x₀-c.A)

theorem start_growth (s : ℝ) : c.growth s c.x₀ = p.intake c.y₀ := by
  simp [growth,sub_ne_zero.mpr c.right.ne']

theorem matched_root (s : ℝ) : p.Root (c.growth s) 0 c.x₀ c.y₀ := by
  refine ⟨?_, by simpa [mul_comm] using c.compatible⟩
  rw [c.start_growth]; exact div_mul_cancel₀ _ (add_pos p.hβ c.posY).ne'

/-- The normalized linear factors are exactly those printed in Section 1. -/
theorem multiplier_ids (x : ℝ) :
    1+c.weakS*(x-c.x₀) = (1+c.α*x)/(1+c.α*c.x₀) ∧
    1+c.strongS*(x-c.x₀) = (x-c.A)/(c.x₀-c.A) := by
  have p0 := c.posA.trans c.left
  have ha := c.alpha_pos
  have dn : 0 < 1+c.α*c.x₀ := by positivity
  constructor <;> simp only [weakS, strongS] <;> field_simp [dn.ne',sub_ne_zero.mpr c.left.ne'] <;> ring

theorem slope_order : 0 < c.weakS ∧ c.weakS < c.strongS := by
  have p0 := c.posA.trans c.left
  have ha := c.alpha_pos
  have dn : 0 < 1+c.α*c.x₀ := by positivity
  exact ⟨div_pos ha dn, (div_lt_div_iff₀ dn (sub_pos.mpr c.left)).2
    (by nlinarith [mul_pos ha c.posA])⟩

theorem growth_deriv_at_start (s : ℝ) :
    HasDerivAt (c.growth s)
      (p.intake c.y₀ * (s-1/(c.K-c.x₀))) c.x₀ := by
  have k := (sub_pos.mpr c.right).ne'
  have hU := ((hasDerivAt_const c.x₀ c.K).sub (hasDerivAt_id c.x₀)).div_const (c.K-c.x₀)
  have hF := (((hasDerivAt_id c.x₀).sub_const c.x₀).const_mul s).const_add 1
  convert (hU.const_mul (p.intake c.y₀)).mul hF using 1 <;>
    first | rfl | (dsimp; field_simp [k]; ring)

theorem growth_gap {s₁ s₂ x : ℝ} (hs : s₁ < s₂) (hx : c.x₀ < x) (hk : x < c.K) :
    c.growth s₁ x < c.growth s₂ x := by
  have hq : 0 < p.intake c.y₀ := div_pos (mul_pos p.hm c.posY) (add_pos p.hβ c.posY)
  exact mul_lt_mul_of_pos_left (add_lt_add_left (mul_lt_mul_of_pos_right hs (sub_pos.mpr hx)) _)
    (mul_pos hq (div_pos (sub_pos.mpr hk) (sub_pos.mpr c.right)))

theorem below_capacity {s h x y : ℝ} (hs : 0 ≤ s) (hx : c.x₀ < x) (hy : 0 < y)
    (r : p.Root (c.growth s) h x y) : x < c.K := by
  have hq : 0 < p.intake c.y₀ := div_pos (mul_pos p.hm c.posY) (add_pos p.hβ c.posY)
  have v := (Params.Root.coords p r hy).1
  have hp : 0 < c.growth s x := v ▸ (div_pos (mul_pos p.hm hy) (add_pos p.hβ hy))
  by_contra! neg
  have ff : 0 ≤ 1+s*(x-c.x₀) := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hx.le)]
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hq.le
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr neg) (sub_pos.mpr c.right).le)) ff)) hp

theorem pair_order {s₁ s₂ H : ℝ} (hH : 0 < H) (hs : s₁ < s₂) (hs₂ : 0 ≤ s₂)
    (L : p.Branch (c.growth s₁) H) (U : p.Branch (c.growth s₂) H)
    (hxL : L.x 0 = c.x₀) (hxU : U.x 0 = c.x₀)
    (hyL : L.y 0 = c.y₀) (hyU : U.y 0 = c.y₀) :
    ∀ h ∈ Ioc 0 H, L.x h < U.x h ∧ L.y h < U.y h := by
  apply p.finite_order hH L U (hxL.trans hxU.symm) (hyL.trans hyU.symm)
  intro h hh hr
  rw [hxU] at hr
  have hm : h ∈ Icc 0 H := ⟨hh.1.le,hh.2⟩
  exact c.growth_gap hs hr (c.below_capacity hs₂ hr (U.posY h hm) (U.root h hm))

/-- Competition supplement Theorem 2, applied to any compact initial segment
    of the common regular branches. A stable branch satisfies these hypotheses. -/
theorem three_model_finite_order {H : ℝ} (hH : 0 < H)
    (L : p.Branch (c.growth 0) H) (W : p.Branch (c.growth c.weakS) H)
    (S : p.Branch (c.growth c.strongS) H)
    (lx : L.x 0 = c.x₀) (wx : W.x 0 = c.x₀) (sx : S.x 0 = c.x₀)
    (ly : L.y 0 = c.y₀) (wy : W.y 0 = c.y₀) (sy : S.y 0 = c.y₀) :
    ∀ h ∈ Ioc 0 H, c.x₀ < L.x h ∧ L.x h < W.x h ∧ W.x h < S.x h ∧
      L.y h < W.y h ∧ W.y h < S.y h := by
  intro h hh
  obtain ⟨w,s⟩ := c.slope_order
  obtain ⟨x₁,y₁⟩ := c.pair_order hH w w.le L W lx wx ly wy h hh
  obtain ⟨x₂,y₂⟩ := c.pair_order hH s (w.trans s).le W S wx sx wy sy h hh
  exact ⟨lx ▸ p.prey_strictMono L ⟨le_rfl,hH.le⟩ ⟨hh.1.le,hh.2⟩ hh.1,x₁,x₂,y₁,y₂⟩

end Calibration

/-! At a common root the predator sensitivity is a strictly increasing
fractional linear function of the prey-growth slope. -/
theorem compare_sensitivities {u₁ u₂ U v V W : ℝ} (hu : u₁ < u₂)
    (hU : 0 < U) (hv : 0 < v) (hW : 0 < W)
    (d₁ : 0 < U*v-V*u₁) (d₂ : 0 < U*v-V*u₂) :
    u₁*W/(U*v-V*u₁) < u₂*W/(U*v-V*u₂) := by
  apply (div_lt_div_iff₀ d₁ d₂).2
  nlinarith only [mul_pos (mul_pos (mul_pos hU hv) hW) (sub_pos.mpr hu)]

namespace Calibration
variable {p : Params} (c : Calibration p)

def initialSlope (s : ℝ) := p.intake c.y₀ * (s - 1/(c.K-c.x₀))
def response (s : ℝ) := (c.initialSlope s * (p.β+c.y₀))*((p.β+c.y₀)*c.y₀) /
  (p.e*p.m*(p.m-p.intake c.y₀) - p.d*(c.initialSlope s*(p.β+c.y₀)))

theorem start_den (s : ℝ) :
    p.scaledDet (c.growth s) 0 c.x₀ c.y₀ =
    p.e*p.m*(p.m-p.intake c.y₀) - p.d*(c.initialSlope s*(p.β+c.y₀)) := by
  unfold Params.scaledDet initialSlope
  rw [c.start_growth, (c.growth_deriv_at_start s).deriv]
  ring

theorem branch_initial_response {s H : ℝ} (hH : 0 ≤ H) (b : p.Branch (c.growth s) H)
    (hx : b.x 0 = c.x₀) (hy : b.y 0 = c.y₀) :
    HasDerivWithinAt b.y (c.response s) (Icc 0 H) 0 := by
  have z := (p.branch_derivatives b (show 0 ∈ Icc 0 H from ⟨le_rfl,hH⟩)).2
  rw [hx,hy,c.start_den,(c.growth_deriv_at_start s).deriv] at z
  exact z

theorem increasing_response {s₁ s₂ : ℝ} (hs : s₁ < s₂)
    (hd₁ : 0 < p.detJ (c.growth s₁) 0 c.x₀ c.y₀)
    (hd₂ : 0 < p.detJ (c.growth s₂) 0 c.x₀ c.y₀) : c.response s₁ < c.response s₂ := by
  have yy := add_pos p.hβ c.posY
  have q : 0 < p.intake c.y₀ := div_pos (mul_pos p.hm c.posY) yy
  have m : p.intake c.y₀ < p.m := (div_lt_iff₀ yy).2 (by nlinarith [mul_pos p.hm p.hβ])
  have hh {s : ℝ} (hd : 0 < p.detJ (c.growth s) 0 c.x₀ c.y₀) :
      0 < p.e*p.m*(p.m-p.intake c.y₀) - p.d*(c.initialSlope s*(p.β+c.y₀)) := by
    rw [p.determinant_eq (c.matched_root s) c.posY, c.start_den] at hd
    exact pos_of_mul_pos_right hd (div_nonneg (mul_nonneg (c.posA.trans c.left).le c.posY.le) (sq_nonneg _))
  apply compare_sensitivities _ (mul_pos p.he p.hm) (sub_pos.mpr m)
    (mul_pos yy c.posY) (hh hd₁) (hh hd₂)
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left (sub_lt_sub_right hs _) q) yy

theorem three_model_local_order
    (hL : 0 < p.detJ (c.growth 0) 0 c.x₀ c.y₀)
    (hW : 0 < p.detJ (c.growth c.weakS) 0 c.x₀ c.y₀)
    (hS : 0 < p.detJ (c.growth c.strongS) 0 c.x₀ c.y₀) :
    c.response 0 < c.response c.weakS ∧ c.response c.weakS < c.response c.strongS :=
  ⟨c.increasing_response c.slope_order.1 hL hW, c.increasing_response c.slope_order.2 hW hS⟩
/-- Direct ordering of the right derivatives of the three actual branch functions. -/
theorem branch_local_order {H : ℝ} (hH : 0 < H)
    (L : p.Branch (c.growth 0) H) (W : p.Branch (c.growth c.weakS) H)
    (S : p.Branch (c.growth c.strongS) H)
    (lx : L.x 0 = c.x₀) (wx : W.x 0 = c.x₀) (sx : S.x 0 = c.x₀)
    (ly : L.y 0 = c.y₀) (wy : W.y 0 = c.y₀) (sy : S.y 0 = c.y₀) :
    derivWithin L.y (Icc 0 H) 0 < derivWithin W.y (Icc 0 H) 0 ∧
    derivWithin W.y (Icc 0 H) 0 < derivWithin S.y (Icc 0 H) 0 := by
  have start : (0:ℝ) ∈ Icc 0 H := ⟨le_rfl,hH.le⟩
  have reg {s : ℝ} (B : p.Branch (c.growth s) H)
      (bx : B.x 0 = c.x₀) (by₀ : B.y 0 = c.y₀) :
      0 < p.detJ (c.growth s) 0 c.x₀ c.y₀ := by
    simpa only [bx,by₀] using B.regular 0 start
  have ud := uniqueDiffOn_Icc hH 0 start
  rw [(c.branch_initial_response hH.le L lx ly).derivWithin ud,
      (c.branch_initial_response hH.le W wx wy).derivWithin ud,
      (c.branch_initial_response hH.le S sx sy).derivWithin ud]
  exact c.three_model_local_order (reg L lx ly) (reg W wx wy) (reg S sx sy)
end Calibration

/-- For decreasing per-capita growth, existence implies uniqueness. In particular
    this applies to both logistic models at any nonnegative competition level. -/
theorem unique_of_decreasing (p : Params) {g : ℝ → ℝ} (hg : StrictAnti g)
    {h x₁ x₂ y₁ y₂ : ℝ} (hh : 0 ≤ h) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (r₁ : p.Root g h x₁ y₁) (r₂ : p.Root g h x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  obtain ⟨g₁,c₁⟩ := Params.Root.coords p r₁ hy₁
  obtain ⟨g₂,c₂⟩ := Params.Root.coords p r₂ hy₂
  have ex {x z y w : ℝ} (cy : x = p.chart h y) (cw : z = p.chart h w)
      (ey : g x = p.intake y) (ew : g z = p.intake w)
      (py : 0 < y) (order : y < w) : False := by
    have hl := p.chart_lt_y hh py.le order
    rw [← cy, ← cw] at hl
    have hbad := hg hl
    rw [ey, ew] at hbad
    exact (not_lt_of_ge (p.intake_lt py.le order).le) hbad
  have eq : y₁ = y₂ := le_antisymm (le_of_not_gt (ex c₂ c₁ g₂ g₁ hy₂))
    (le_of_not_gt (ex c₁ c₂ g₁ g₂ hy₁))
  exact ⟨by rw [c₁,c₂,eq],eq⟩

/-- Section 4 of the general comparison supplement. The four named feeding
laws use the same positive numerator and two nonnegative denominator terms. -/
structure Feeding where
  a : ℝ
  b : ℝ
  c : ℝ
  e : ℝ
  d : ℝ
  ha : 0 < a
  hb : 0 ≤ b
  hc : 0 ≤ c
  he : 0 < e
  hd : 0 < d

namespace Feeding
variable (f : Feeding)
def denom (x y : ℝ) := 1 + f.b*x + f.c*y
def intake (x y : ℝ) := f.a*y/f.denom x y
def gain (x y : ℝ) := f.e*f.a*x/f.denom x y
def Root (g : ℝ → ℝ) (h x y : ℝ) : Prop :=
  g x = f.intake x y ∧ f.gain x y = f.d+h*y

theorem denom_pos {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 < f.denom x y := by
  unfold denom
  linarith [mul_nonneg f.hb hx,mul_nonneg f.hc hy]

theorem intake_strict_y {x v w : ℝ} (hx : 0 ≤ x) (hv : 0 ≤ v) (hw : v < w) :
    f.intake x v < f.intake x w := by
  apply (div_lt_div_iff₀ (f.denom_pos hx hv) (f.denom_pos hx (hv.trans hw.le))).2
  unfold denom
  nlinarith only [mul_pos f.ha (mul_pos (show 0 < 1+f.b*x by linarith [mul_nonneg f.hb hx])
    (sub_pos.mpr hw))]

theorem gain_strict_x {x z y : ℝ} (hx : 0 ≤ x) (hxz : x < z) (hy : 0 ≤ y) :
    f.gain x y < f.gain z y := by
  apply (div_lt_div_iff₀ (f.denom_pos hx hy) (f.denom_pos (hx.trans hxz.le) hy)).2
  unfold denom
  nlinarith only [mul_pos (mul_pos f.he f.ha) (mul_pos
    (show 0 < 1+f.c*y by linarith [mul_nonneg f.hc hy]) (sub_pos.mpr hxz))]

theorem gain_anti_y {x v w : ℝ} (hx : 0 ≤ x) (hv : 0 ≤ v) (hw : v ≤ w) :
    f.gain x w ≤ f.gain x v := by
  apply (div_le_div_iff₀ (f.denom_pos hx (hv.trans hw)) (f.denom_pos hx hv)).2
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_pos f.he f.ha).le hx)
  unfold denom
  exact add_le_add_left (mul_le_mul_of_nonneg_left hw f.hc) _

/-- Both population orders for the four-law family, under the rightward
condition stated in the general theorem. The equations hold only on the
selected graph. No uniqueness from other coexistence roots is assumed. -/
theorem four_law_order {g₁ g₂ x₁ x₂ y₁ y₂ : ℝ → ℝ} {H : ℝ}
    (_hH : 0 < H) (cx : ContinuousOn x₁ (Icc 0 H))
    (startX : x₁ 0 = x₂ 0) (_startY : y₁ 0 = y₂ 0)
    (r₁ : ∀ t ∈ Icc 0 H, 0 < x₁ t ∧ 0 < y₁ t ∧ f.Root g₁ t (x₁ t) (y₁ t))
    (r₂ : ∀ t ∈ Icc 0 H, 0 < x₂ t ∧ 0 < y₂ t ∧ f.Root g₂ t (x₂ t) (y₂ t))
    (right : ∀ h ∈ Ioc 0 H, x₂ 0 < x₂ h)
    (gap : ∀ h ∈ Ioc 0 H, x₂ 0 < x₂ h → g₁ (x₂ h) < g₂ (x₂ h)) :
    ∀ h ∈ Ioc 0 H, x₁ h < x₂ h ∧ y₁ h < y₂ h := by
  intro h hh
  have hh' : h ∈ Icc 0 H := ⟨hh.1.le,hh.2⟩
  obtain ⟨px,py,g₂e,p₂e⟩ := r₂ h hh'
  have lessX : x₁ h < x₂ h := by
    apply lt_of_not_ge
    intro rev
    obtain ⟨t,ht,hit⟩ := intermediate_value_Icc hh.1.le (cx.mono (Icc_subset_Icc_right hh.2))
      (show x₂ h ∈ Icc (x₁ 0) (x₁ h) from ⟨startX ▸ (right h hh).le,rev⟩)
    obtain ⟨_,qy,g₁e,p₁e⟩ := r₁ t ⟨ht.1,ht.2.trans hh.2⟩
    rw [hit] at g₁e p₁e
    have dg := gap h hh (right h hh)
    rw [g₁e,g₂e] at dg
    have ly : y₁ t < y₂ h := by
      by_contra! le
      rcases le.eq_or_lt with he | he
      · rw [he] at dg; exact (lt_irrefl _) dg
      · exact (not_lt_of_ge dg.le) (f.intake_strict_y px.le py.le he)
    have anti := f.gain_anti_y px.le qy.le ly.le
    rw [p₁e,p₂e] at anti
    have rhs := (mul_le_mul_of_nonneg_right ht.2 qy.le).trans_lt
      (mul_lt_mul_of_pos_left ly hh.1)
    linarith
  refine ⟨lessX, ?_⟩
  apply lt_of_not_ge
  intro rev
  obtain ⟨qx,qy,_,p₁e⟩ := r₁ h hh'
  have crossed := (f.gain_anti_y qx.le py.le rev).trans_lt
    (f.gain_strict_x qx.le lessX py.le)
  rw [p₁e,p₂e] at crossed
  linarith [mul_le_mul_of_nonneg_left rev hh.1.le]

end Feeding

/-- The calibrated logistic rate is decreasing everywhere. -/
theorem Calibration.logistic_decreasing {p : Params} (c : Calibration p) :
    StrictAnti (c.growth 0) := by
  intro x z h
  have hp : 0 < p.intake c.y₀ := div_pos (mul_pos p.hm c.posY) (add_pos p.hβ c.posY)
  simp only [Calibration.growth,zero_mul,add_zero,mul_one]
  exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right (sub_lt_sub_left h _) (sub_pos.mpr c.right)) hp

/-- Coefficient restriction behind the three-root bound for positive
competition. This is the sign step in supplementary equation S2. -/
theorem allee_coeff_order {B C s k : ℝ} (hC : 0 < C) (hs : 0 < s) (hk : 0 < k)
    (h₃ : 0 ≤ B*s*k-C*s^2*(1+6*k+3*k^2)) :
    0 < B*s*(1+2*k)-C*s^2*(3+6*k+k^2) := by
  have h1 : 0 < 1+2*k := by positivity
  have h2 : 0 < C*s^2*(1+5*k+9*k^2+5*k^3) := by positivity
  apply pos_of_mul_pos_right (a := k)
  · nlinarith only [h2,mul_nonneg h₃ h1.le]
  · exact hk.le

#print axioms Feeding.four_law_order
#print axioms Calibration.logistic_decreasing
#print axioms allee_coeff_order

namespace Count
open Polynomial
open scoped Polynomial

/-- Positive roots are counted with their algebraic multiplicities. -/
def positiveRoots (P : ℝ[X]) := P.roots.filter (fun z => 0 < z)

private theorem takeRoot {M : Multiset ℝ} (h : 0 < M.card) :
    ∃ u N, M = u ::ₘ N := by
  obtain ⟨u,hu⟩ := Multiset.card_pos_iff_exists_mem.mp h
  obtain ⟨N,k⟩ := Multiset.exists_cons_of_mem hu
  exact ⟨u,N,k⟩

private theorem quartet (P : ℝ[X]) (h : 3 < (positiveRoots P).card) :
    ∃ u v w z : ℝ, 0<u ∧ 0<v ∧ 0<w ∧ 0<z ∧
      (X-C u)*(X-C v)*(X-C w)*(X-C z) ∣ P := by
  classical
  obtain ⟨u,N₁,e₁⟩ := takeRoot (show 0 < (positiveRoots P).card by omega)
  rw [e₁,Multiset.card_cons] at h
  obtain ⟨v,N₂,e₂⟩ := takeRoot (show 0 < N₁.card by omega)
  rw [e₂,Multiset.card_cons] at h
  obtain ⟨w,N₃,e₃⟩ := takeRoot (show 0 < N₂.card by omega)
  rw [e₃,Multiset.card_cons] at h
  obtain ⟨z,N₄,e₄⟩ := takeRoot (show 0 < N₃.card by omega)
  rw [e₂,e₃,e₄] at e₁
  let M := u ::ₘ v ::ₘ w ::ₘ z ::ₘ (0 : Multiset ℝ)
  have sub : M ≤ positiveRoots P := by
    rw [e₁]
    exact Multiset.cons_le_cons _ (Multiset.cons_le_cons _ (Multiset.cons_le_cons _
      (Multiset.cons_le_cons _ (zero_le _))))
  have pos {a : ℝ} (ha : a ∈ M) : 0 < a :=
    (Multiset.mem_filter.mp (Multiset.mem_of_le sub ha)).2
  refine ⟨u,v,w,z,pos (by simp [M]),pos (by simp [M]),pos (by simp [M]),
    pos (by simp [M]),?_⟩
  have le : M ≤ P.roots := sub.trans (Multiset.filter_le _ _)
  have dv := (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map (f := fun a : ℝ => X-C a) le)).trans
    P.prod_multiset_X_sub_C_dvd
  simpa [M,mul_assoc] using dv

/-- A quintic with the sign pattern in the supplementary count proof has at
most three positive roots, including multiplicities. Four positive factors
would force a positive cubic coefficient and a negative quadratic coefficient. -/
theorem bound_of_coefficients (P : ℝ[X]) (deg : P.natDegree ≤ 5)
    (h₅ : P.coeff 5 < 0) (h₄ : P.coeff 4 < 0)
    (signs : 0 ≤ P.coeff 3 → 0 < P.coeff 2) : (positiveRoots P).card ≤ 3 := by
  classical
  by_contra! many
  obtain ⟨u,v,w,z,hu,hv,hw,hz,Q,eq⟩ := quartet P many
  have nq : Q ≠ 0 := by
    rintro rfl
    simp [eq] at h₅
  have d : ((X-C u)*(X-C v)*(X-C w)*(X-C z) : ℝ[X]).natDegree = 4 := by compute_degree!
  have n : ((X-C u)*(X-C v)*(X-C w)*(X-C z) : ℝ[X]) ≠ 0 := by
    intro he
    simp [he] at d
  rw [eq,natDegree_mul n nq,d] at deg
  obtain ⟨l,m,lq⟩ := exists_eq_X_add_C_of_natDegree_le_one (show Q.natDegree ≤ 1 by omega)
  let A := u+v+w+z
  let B := u*v+u*w+u*z+v*w+v*z+w*z
  let D := u*v*w+u*v*z+u*w*z+v*w*z
  let E := u*v*w*z
  have dataP : P = C l*X^5 + C (m-l*A)*X^4 + C (l*B-m*A)*X^3 +
      C (m*B-l*D)*X^2 + C (l*E-m*D)*X+C (m*E) := by
    rw [eq,lq]
    simp only [A,B,D,E,map_add,map_sub,map_mul]
    ring
  have coeffs : P.coeff 5 = l ∧ P.coeff 4 = m-l*A ∧ P.coeff 3 = l*B-m*A ∧
      P.coeff 2 = m*B-l*D := by
    rw [dataP]
    simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
    norm_num
  obtain ⟨e₅,e₄,e₃,e₂⟩ := coeffs
  rw [e₅] at h₅
  rw [e₄] at h₄
  have a : 0 < A := by dsimp [A]; positivity
  have b : 0 < B := by dsimp [B]; positivity
  have ab : 0 < A^2-B := by dsimp [A,B]; ring_nf; positivity
  have bd : 0 < A*B-D := by dsimp [A,B,D]; ring_nf; positivity
  have p3 : 0 ≤ P.coeff 3 := by
    rw [e₃]
    nlinarith only [mul_neg_of_neg_of_pos h₅ ab, mul_neg_of_neg_of_pos h₄ a]
  have p2 := signs p3
  rw [e₂] at p2
  nlinarith only [p2, mul_neg_of_neg_of_pos h₅ bd, mul_neg_of_neg_of_pos h₄ b]

/-- The equilibrium polynomial for g(x)=a+b*x-c*x² in the coordinate
z=y/β. This includes weak and strong Allee growth with c>0. -/
def alleePoly (a b c s k m : ℝ) : ℝ[X] :=
  let G := C s*(1+X)*(1+C k*X)
  (1+X)*(C a+C b*G-C c*G^2)-C m*X

theorem eval_alleePoly (a b c s k m z : ℝ) :
    (alleePoly a b c s k m).eval z =
    (1+z)*(a+b*(s*(1+z)*(1+k*z))-c*(s*(1+z)*(1+k*z))^2)-m*z := by
  simp [alleePoly]

/-- The bound is three for k=0 and for positive competition k>0. -/
theorem allee_at_most_three (a b c s k m : ℝ) (hc : 0<c) (hs : 0<s) (hk : 0≤k) :
    (positiveRoots (alleePoly a b c s k m)).card ≤ 3 := by
  rcases hk.eq_or_lt with h | h
  · subst k
    have lim : (alleePoly a b c s 0 m).natDegree ≤ 3 := by
      simp [alleePoly]
      compute_degree!
    exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans
      ((Polynomial.card_roots' _).trans lim)
  · let P := alleePoly a b c s k m
    have co : P = C (a+b*s-c*s^2) +
        C (a+b*s*(2+k)-c*s^2*(3+2*k)-m)*X +
        C (b*s*(1+2*k)-c*s^2*(3+6*k+k^2))*X^2 +
        C (b*s*k-c*s^2*(1+6*k+3*k^2))*X^3 +
        C (-c*s^2*(2*k+3*k^2))*X^4 + C (-c*s^2*k^2)*X^5 := by
      simp only [P,alleePoly,map_sub,map_add,map_mul,map_pow,map_neg,map_one,map_ofNat]
      ring
    apply bound_of_coefficients
    · dsimp [P,alleePoly]; compute_degree!
    · change P.coeff 5 < 0
      rw [co]
      simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
      norm_num
      positivity
    · change P.coeff 4 < 0
      rw [co]
      simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
      norm_num
      positivity
    · change 0 ≤ P.coeff 3 → 0 < P.coeff 2
      rw [co]
      simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
      convert
        (allee_coeff_order (B := b) hc hs h) using 1 <;> norm_num

theorem root_iff_poly (p : Params) (a b c h z : ℝ) :
    p.Root (fun x => a+b*x-c*x^2) h (p.chart h (p.β*z)) (p.β*z) ↔
    (alleePoly a b c (p.β*p.d/(p.e*p.m)) (h*p.β/p.d) p.m).eval z = 0 := by
  have ec := (mul_pos p.he p.hm).ne'
  have chart_eq : p.chart h (p.β*z) = (p.β*p.d/(p.e*p.m))*(1+z)*(1+(h*p.β/p.d)*z) := by
    unfold Params.chart
    field_simp [ec,p.hd.ne']; ring
  rw [eval_alleePoly,←chart_eq]
  unfold Params.Root
  have hp : p.e*p.m*p.chart h (p.β*z) = (p.β+p.β*z)*(p.d+h*(p.β*z)) := by
    unfold Params.chart
    field_simp [ec]
  constructor
  · intro eq
    have eqx := eq.1
    apply (mul_left_cancel₀ p.hβ.ne')
    linear_combination eqx
  · intro eq
    exact ⟨by linear_combination p.β*eq,hp⟩

/-- Exact signs on three adjacent intervals certify three distinct roots. -/
private theorem three_brackets (P : ℝ[X]) {a b c d : ℝ}
    (ha : 0<a) (hab : a<b) (hbc : b<c) (hcd : c<d)
    (sa : 0<P.eval a) (sb : P.eval b<0) (sc : 0<P.eval c) (sd : P.eval d<0) :
    ∃ u v w, 0<u ∧ u<v ∧ v<w ∧ P.eval u=0 ∧ P.eval v=0 ∧ P.eval w=0 := by
  obtain ⟨u,hu,su⟩ := intermediate_value_Ioo' hab.le P.continuousOn ⟨sb,sa⟩
  obtain ⟨v,hv,sv⟩ := intermediate_value_Ioo hbc.le P.continuousOn ⟨sb,sc⟩
  obtain ⟨w,hw,sw⟩ := intermediate_value_Ioo' hcd.le P.continuousOn ⟨sd,sc⟩
  exact ⟨u,v,w,ha.trans hu.1,hu.2.trans hv.1,hv.2.trans hw.1,su,sv,sw⟩

/-- The M0 and M4 examples in supplementary Table S2.5 have three roots. -/
theorem weak_three_example (k : ℝ) (caseK : k=0 ∨ k=32/45045) :
    let P := alleePoly (1/5) (27/200) (1/50) (33/76) k (399/800)
    ∃ u v w, 0<u ∧ u<v ∧ v<w ∧ P.eval u=0 ∧ P.eval v=0 ∧ P.eval w=0 := by
  apply three_brackets _ (a := 3) (b := 7/2) (c := 9/2) (d := 6) <;>
    rcases caseK with rfl | rfl <;> norm_num [eval_alleePoly]

/-- The M2 and M5 examples use the same two competition levels, h=0 and
h=1/10000, with the strong-growth predator parameters. -/
theorem strong_three_example (k : ℝ) (caseK : k=0 ∨ k=216/635375) :
    let P := alleePoly (-1/5) (1/8) (1/80) (782/369) k (41/192)
    ∃ u v w, 0<u ∧ u<v ∧ v<w ∧ P.eval u=0 ∧ P.eval v=0 ∧ P.eval w=0 := by
  apply three_brackets _ (a := 1/4) (b := 1/2) (c := 3/4) (d := 1) <;>
    rcases caseK with rfl | rfl <;> norm_num [eval_alleePoly]

end Count
#print axioms Count.root_iff_poly
#print axioms Count.weak_three_example
#print axioms Count.strong_three_example
#print axioms Count.allee_at_most_three

#print axioms Params.root_iff
#print axioms Params.determinant_eq
#print axioms Params.branch_derivatives
#print axioms Params.finite_order
#print axioms Calibration.three_model_finite_order
#print axioms Calibration.three_model_local_order
#print axioms Calibration.branch_local_order
#print axioms Calibration.branch_initial_response
#print axioms unique_of_decreasing

end Direction2
