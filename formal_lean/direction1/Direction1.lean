import D1Core
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Filter Set
open scoped Topology
namespace Direction1

/-- The two components use the original time scale. -/
def q (g : ℝ → ℝ) (K x : ℝ) := g x * (1 - x / K)
def prey (g p : ℝ → ℝ) (K x y : ℝ) := x * q g K x - y * p (y / x)
def predator (p : ℝ → ℝ) (e d x y : ℝ) := y * (e * p (y / x) - d)

structure Jacobian2 where
  xx : ℝ
  xy : ℝ
  yx : ℝ
  yy : ℝ

def Jacobian2.trace (J : Jacobian2) := J.xx + J.yy
def Jacobian2.det (J : Jacobian2) := J.xx * J.yy - J.xy * J.yx

def jac (g p : ℝ → ℝ) (e d K x y : ℝ) : Jacobian2 :=
  ⟨deriv (fun t => prey g p K t y) x, deriv (fun t => prey g p K x t) y,
   deriv (fun t => predator p e d t y) x, deriv (fun t => predator p e d x t) y⟩

def equilibrium (g p : ℝ → ℝ) (e d K x y : ℝ) : Prop :=
  prey g p K x y = 0 ∧ predator p e d x y = 0

theorem equilibrium_iff {g p : ℝ → ℝ} {e d K x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    equilibrium g p e d K x y ↔ q g K x = y / x * p (y / x) ∧ e * p (y/x) = d := by
  unfold equilibrium prey predator
  constructor
  · rintro ⟨h₁,h₂⟩
    refine ⟨?_, ?_⟩
    · field_simp [ne_of_gt hx]
      nlinarith only [h₁]
    · rcases mul_eq_zero.mp h₂ with h | h
      · exact (hy.ne' h).elim
      · linarith
  · rintro ⟨h₁,h₂⟩
    rw [h₁, h₂]
    constructor <;> field_simp [hx.ne'] <;> ring

def qx (g : ℝ → ℝ) (K x : ℝ) := deriv g x * (1-x/K) - g x/K

theorem q_deriv {g : ℝ → ℝ} {K x : ℝ} (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (q g K) (qx g K x) x := by
  convert hg.hasDerivAt.mul ((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).div_const K)) using 1 <;>
    simp [q, qx, id] <;> ring

theorem jac_on_ray {g p : ℝ → ℝ} {e d K x r : ℝ} (hx : x ≠ 0)
    (hg : DifferentiableAt ℝ g x) (hp : DifferentiableAt ℝ p r)
    (he : e * p r = d) (hQ : q g K x = r * p r) :
    jac g p e d K x (r*x) =
    ⟨r*p r + x*qx g K x + r^2*deriv p r, -p r-r*deriv p r,
     -e*r^2*deriv p r, e*r*deriv p r⟩ := by
  have hr : r*x/x = r := by field_simp
  have hp' : HasDerivAt p (deriv p r) (r*x/x) := by rw [hr]; exact hp.hasDerivAt
  have rx := hp'.comp x ((hasDerivAt_const x (r*x)).div (hasDerivAt_id x) hx)
  have ry := hp'.comp (r*x) ((hasDerivAt_id (r*x)).div_const x)
  have h₁ := ((hasDerivAt_id x).mul (q_deriv (K := K) hg)).sub (rx.const_mul (r*x))
  have h₂ := (hasDerivAt_const (r*x) (x*q g K x)).sub ((hasDerivAt_id (r*x)).mul ry)
  have h₃ := (((rx.const_mul e).sub (hasDerivAt_const x d)).const_mul (r*x))
  have h₄ := (hasDerivAt_id (r*x)).mul ((ry.const_mul e).sub (hasDerivAt_const (r*x) d))
  unfold jac
  congr 1
  · change deriv (fun t => t*q g K t - (r*x)*p ((r*x)/t)) x = _
    rw [show deriv (fun t => t*q g K t - (r*x)*p ((r*x)/t)) x = _ from h₁.deriv]
    simp [id, hr, hQ, Function.comp_def]
    field_simp [hx] <;> ring
  · change deriv (fun t => x*q g K x - t*p (t/x)) (r*x) = _
    rw [show deriv (fun t => x*q g K x - t*p (t/x)) (r*x) = _ from h₂.deriv]
    simp [id, hr, Function.comp_def]
    field_simp [hx] <;> ring
  · change deriv (fun t => (r*x)*(e*p ((r*x)/t)-d)) x = _
    rw [show deriv (fun t => (r*x)*(e*p ((r*x)/t)-d)) x = _ from h₃.deriv]
    simp [id, hr, Function.comp_def]
    field_simp [hx] <;> ring
  · change deriv (fun t => t*(e*p (t/x)-d)) (r*x) = _
    rw [show deriv (fun t => t*(e*p (t/x)-d)) (r*x) = _ from h₄.deriv]
    simp [id, hr, Function.comp_def, he]
    field_simp [hx] <;> ring

theorem trace_det {g p : ℝ → ℝ} {e d K x r : ℝ} (hx : x ≠ 0)
    (hg : DifferentiableAt ℝ g x) (hp : DifferentiableAt ℝ p r)
    (he : e * p r = d) (hQ : q g K x = r * p r) :
    (jac g p e d K x (r*x)).trace = x*qx g K x + r*p r+r*(r+e)*deriv p r ∧
    (jac g p e d K x (r*x)).det = e*r*deriv p r*x*qx g K x := by
  rw [jac_on_ray hx hg hp he hQ]
  constructor <;> simp [Jacobian2.trace,Jacobian2.det] <;> ring

/-- Parameterization of the equilibrium curve by prey density. -/
def cap (g : ℝ → ℝ) (Q x : ℝ) := x/(1-Q/g x)
def E (g : ℝ → ℝ) (x : ℝ) := x*deriv g x/g x
def D (g : ℝ → ℝ) (Q x : ℝ) := g x-(1+E g x)*Q

theorem q_cap {g : ℝ → ℝ} {Q x : ℝ} (hx : x ≠ 0) (hg : g x ≠ 0) (hh : Q < g x) :
    q g (cap g Q x) x = Q := by
  have hd : 1-Q/g x ≠ 0 := by intro h; field_simp [hg] at h; linarith
  unfold q cap
  field_simp [hx, hg, hd] <;> ring

theorem x_qx_eq {g : ℝ → ℝ} {K x Q : ℝ} (hK : K ≠ 0) (hg : g x ≠ 0)
    (hq : q g K x = Q) : x * qx g K x = -D g Q x := by
  rw [← hq]
  unfold qx D E q
  field_simp [hg, hK] <;> ring

theorem ray_trace {g p : ℝ → ℝ} {e d x r Q : ℝ} (hx : 0 < x) (hg : 0 < g x)
    (hq : Q < g x) (hgr : DifferentiableAt ℝ g x) (hp : DifferentiableAt ℝ p r)
    (he : e*p r = d) (hl : Q = r*p r) :
    (jac g p e d (cap g Q x) x (r*x)).trace = -D g Q x + Q + r*(r+e)*deriv p r := by
  have hC := q_cap hx.ne' hg.ne' hq
  have hK : 0 < cap g Q x := div_pos hx (sub_pos.mpr ((div_lt_one hg).mpr hq))
  rw [(trace_det hx.ne' hgr hp he (hC.trans hl)).1, x_qx_eq hK.ne' hg.ne' hC, ← hl]

theorem capacity_deriv {g : ℝ → ℝ} {Q x : ℝ} (hg : 0 < g x)
    (hq : Q < g x) (hd : DifferentiableAt ℝ g x) :
    HasDerivAt (cap g Q) (D g Q x/(g x*(1-Q/g x)^2)) x := by
  have hne : 1-Q/g x ≠ 0 := (sub_pos.mpr ((div_lt_one hg).mpr hq)).ne'
  have hh := (hasDerivAt_id x).div ((hasDerivAt_const x (1:ℝ)).sub
    ((hasDerivAt_const x Q).div hd.hasDerivAt hg.ne')) hne
  convert hh using 1
  change D g Q x / (g x*(1-Q/g x)^2) = _
  rw [← div_div]
  apply congrArg (fun z : ℝ => z/(1-Q/g x)^2)
  simp only [id_eq, one_mul,zero_mul, zero_sub, D,E]
  field_simp [hg.ne']
  ring

theorem elasticity_deriv {g : ℝ → ℝ} {x : ℝ}
    (hg : g x ≠ 0) (h₁ : DifferentiableAt ℝ g x) (h₂ : DifferentiableAt ℝ (deriv g) x) :
    HasDerivAt (E g) (D1Core.elasticityPrime x (g x) (deriv g x) (deriv (deriv g) x)) x := by
  convert ((hasDerivAt_id x).mul h₂.hasDerivAt).div h₁.hasDerivAt hg using 1 <;>
    simp [E,D1Core.elasticityPrime,id] <;> field_simp [hg] <;> ring

def rayT (g p : ℝ → ℝ) (e d r Q x : ℝ) :=
  (jac g p e d (cap g Q x) x (r*x)).trace

/-- The differential dT/dK along the local equilibrium curve parameterized by x.
`chart_trace` below interprets this quotient in the physical parameter K. -/
def slopeK (g p : ℝ → ℝ) (e d r Q s : ℝ) :=
  deriv (rayT g p e d r Q) s / deriv (cap g Q) s

theorem ray_deriv {g p : ℝ → ℝ} {e d r Q s : ℝ}
    (hs : 0 < s) (hg : 0 < g s) (hq : Q < g s)
    (h₁ : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t) (h₂ : DifferentiableAt ℝ (deriv g) s)
    (hp : DifferentiableAt ℝ p r) (he : e*p r = d) (hl : Q = r*p r) :
    HasDerivAt (rayT g p e d r Q)
      (Q * D1Core.elasticityPrime s (g s) (deriv g s) (deriv (deriv g) s) - deriv g s) s := by
  have hd := h₁.self_of_nhds
  have hel := elasticity_deriv hg.ne' hd h₂
  have hD := hd.hasDerivAt.sub (((hasDerivAt_const s (1:ℝ)).add hel).mul_const Q)
  have hbase := (hD.neg.add (hasDerivAt_const s Q)).add (hasDerivAt_const s (r*(r+e)*deriv p r))
  apply HasDerivAt.congr_of_eventuallyEq (f := fun x => -D g Q x + Q + r*(r+e)*deriv p r)
  · convert hbase using 1 <;> ring
  · filter_upwards [h₁, Ioi_mem_nhds hs, hd.continuousAt.tendsto (Ioi_mem_nhds hg),
        hd.continuousAt.tendsto (Ioi_mem_nhds hq)] with t ht ht₁ ht₂ ht₃
    exact ray_trace ht₁ ht₂ ht₃ ht hp he hl

theorem slopeK_neg_iff {g p : ℝ → ℝ} {e d r Q s : ℝ}
    (hs : 0 < s) (hg : 0 < g s) (hq : Q < g s) (hD : 0 < D g Q s)
    (h₁ : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t) (h₂ : DifferentiableAt ℝ (deriv g) s)
    (hp : DifferentiableAt ℝ p r) (he : e*p r = d) (hl : Q = r*p r) :
    slopeK g p e d r Q s < 0 ↔
    Q * D1Core.elasticityPrime s (g s) (deriv g s) (deriv (deriv g) s) - deriv g s < 0 := by
  have hdn : 0 < 1-Q/g s := sub_pos.mpr ((div_lt_one hg).mpr hq)
  have hk : 0 < deriv (cap g Q) s := by
    rw [(capacity_deriv hg hq h₁.self_of_nhds).deriv]
    positivity
  unfold slopeK
  rw [(ray_deriv hs hg hq h₁ h₂ hp he hl).deriv, div_neg_iff]
  simp [hk, not_lt_of_ge hk.le]

structure Admissible (p : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 1 p (Ioi 0)
  positive : ∀ r > 0, 0 < p r
  decreasing : StrictAntiOn p (Ioi 0)

theorem intake_deriv {p : ℝ → ℝ} (hp : Admissible p) {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ p r ∧ deriv p r ≤ 0 := by
  have hd : DifferentiableAt ℝ p r :=
    ((hp.smooth r hr).contDiffAt (Ioi_mem_nhds hr)).differentiableAt (by norm_num)
  refine ⟨hd, le_of_tendsto hd.hasDerivAt.tendsto_slope_zero_right ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have hpdec := hp.decreasing hr (show 0 < r+t by linarith) (show r < r+t by linarith)
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht'.le) (sub_nonpos.mpr hpdec.le)

/-- Every load in the open interval is achieved by a globally positive, decreasing
intake on the positive ratio axis. -/
def holling (e d r z : ℝ) := (2*d/e)/(1+z/r)

theorem holling_admissible {e d r : ℝ} (he : 0 < e) (hd : 0 < d) (hr : 0 < r) :
    Admissible (holling e d r) := by
  constructor
  · apply contDiffOn_const.div ((contDiffOn_const.add (contDiffOn_id.div_const r)))
    intro x hx
    have hh : 0 < x := hx
    positivity
  · intro z hz
    unfold holling
    positivity
  · intro a ha b hb hab
    have ha' : 0 < a := ha
    unfold holling
    exact div_lt_div_of_pos_left (by positivity) (by positivity)
      (add_lt_add_left (div_lt_div_of_pos_right hab hr) 1)

theorem holling_at {e d r : ℝ} (he : 0 < e) (hd : 0 < d) (hr : 0 < r) :
    e * holling e d r r = d ∧ deriv (holling e d r) r = -d/(2*e*r) := by
  have h₀ : 1+r/r ≠ 0 := by simp [hr.ne']
  constructor
  · unfold holling
    field_simp [hr.ne',he.ne'] <;> ring
  · have h := (hasDerivAt_const r (2*d/e)).div
      ((hasDerivAt_const r (1:ℝ)).add ((hasDerivAt_id r).div_const r)) h₀
    change deriv (fun z => 2*d/e/(1+z/r)) r = _
    rw [show deriv (fun z => 2*d/e/(1+z/r)) r = _ from h.deriv]
    simp [id, hr.ne'] <;> field_simp <;> ring

theorem upper_iff {g : ℝ → ℝ} {s Q : ℝ} (hs : 0<s) (hg : 0<g s) (hg' : 0<deriv g s) :
    Q < D1Core.upper s (g s) (deriv g s) ↔ 0 < D g Q s := by
  have h : 0 < 1+s*deriv g s/g s := by positivity
  unfold D1Core.upper D E
  rw [lt_div_iff₀ h]; constructor <;> intro h' <;> nlinarith

theorem upper_lt {s a b : ℝ} (hs : 0<s) (ha : 0<a) (hb : 0<b) : D1Core.upper s a b < a := by
  unfold D1Core.upper
  have h : 0<s*b/a := by positivity
  apply (div_lt_iff₀ (show 0<1+s*b/a by linarith)).mpr
  nlinarith [mul_pos ha h]

theorem capacity_of_q {g : ℝ → ℝ} {K x Q : ℝ} (hK : K ≠ 0) (hx : x ≠ 0) (hg : g x ≠ 0)
    (hq : q g K x = Q) : K = cap g Q x := by
  unfold q at hq
  have hden : 1-Q/g x = x/K := by rw [←hq]; field_simp [hg,hK]; ring
  unfold cap
  rw [hden]
  field_simp [hK,hx]

/-- Structural reduction at *every* nonsaddle coexistence point. -/
theorem reduce_equilibrium {g p : ℝ → ℝ} {e d K s v : ℝ} (hs : 0<s) (hv : 0<v)
    (he : 0<e) (hK : 0<K) (hg : 0<g s) (hgd : DifferentiableAt ℝ g s)
    (hp : Admissible p) (eq : equilibrium g p e d K s v)
    (hdet : 0<(jac g p e d K s v).det) :
    let r := v/s
    let Q := r*p r
    0 < Q ∧ Q < g s ∧ 0 < D g Q s ∧ e*p r=d ∧ K=cap g Q s := by
  let r := v/s
  let Q := r*p r
  have hr : 0<r := div_pos hv hs
  have hQ : 0<Q := mul_pos hr (hp.positive r hr)
  obtain ⟨hq,hbreak⟩ := (equilibrium_iff hs hv).mp eq
  have hbase : q g K s = Q := hq
  have hmul : r*s = v := div_mul_cancel₀ _ hs.ne'
  have j := (trace_det hs.ne' hgd (intake_deriv hp hr).1 hbreak hbase).2
  rw [hmul] at j
  rw [j] at hdet
  have hneg : qx g K s < 0 := by
    by_contra! hh
    have hn := (intake_deriv hp hr).2
    have hz : e*r*deriv p r*s*qx g K s ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hn) hs.le) hh
    linarith
  have hD : 0<D g Q s := by
    have := x_qx_eq hK.ne' hg.ne' hbase
    linarith [mul_neg_of_pos_of_neg hs hneg]
  have hlt : Q<g s := by
    unfold q at hbase
    nlinarith [mul_pos hg (div_pos hs hK)]
  exact ⟨hQ,hlt,hD,hbreak,capacity_of_q hK.ne' hs.ne' hg.ne' hbase⟩

theorem realization {g : ℝ → ℝ} {e d s Q : ℝ} (he : 0<e) (hd : 0<d)
    (hs : 0<s) (hg : 0<g s) (hb : 0<deriv g s) (hgd : DifferentiableAt ℝ g s)
    (hQ : 0<Q) (hU : Q < D1Core.upper s (g s) (deriv g s)) :
    let r := e*Q/d
    let K := cap g Q s
    let p := holling e d r
    0<r ∧ 0<K ∧ e*p r=d ∧ Q=r*p r ∧ Admissible p ∧
      equilibrium g p e d K s (r*s) ∧ 0<(jac g p e d K s (r*s)).det := by
  let r := e*Q/d
  let p := holling e d r
  have hr : 0<r := div_pos (mul_pos he hQ) hd
  have hlt := hU.trans (upper_lt hs hg hb)
  have hD := (upper_iff hs hg hb).mp hU
  have hK : 0 < cap g Q s := div_pos hs (sub_pos.mpr ((div_lt_one hg).mpr hlt))
  obtain ⟨hbreak,hpder⟩ := holling_at he hd hr
  have hpr : p r = d/e := (eq_div_iff he.ne').mpr (by linarith)
  have hload : Q = r*p r := by rw [hpr]; dsimp [r]; field_simp
  have had := holling_admissible he hd hr
  have hq := q_cap hs.ne' hg.ne' hlt
  have hρ : r*s/s=r := by field_simp
  have hv := mul_pos hr hs
  refine ⟨hr,hK,hbreak,hload,had, (equilibrium_iff hs hv).mpr ?_,?_⟩
  · change q g (cap g Q s) s = r*s/s*p (r*s/s) ∧ e*p (r*s/s)=d
    rw [hρ, hq]; exact ⟨hload,hbreak⟩
  · rw [(trace_det hs.ne' hgd (intake_deriv had hr).1 hbreak (hq.trans hload)).2]
    have hqx : s*qx g (cap g Q s) s < 0 := by rw [x_qx_eq hK.ne' hg.ne' hq]; linarith
    have hprneg : deriv p r < 0 := by change deriv (holling e d r) r < 0; rw [hpder]; exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hd) (by positivity)
    have hh := mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (mul_pos he hr) hprneg) hqx
    linarith only [hh]

/-- The paper's universal quantifier over intakes and realizable equilibrium points. -/
def EveryTraceFalls (g : ℝ → ℝ) (e d s : ℝ) : Prop :=
  ∀ p : ℝ → ℝ, Admissible p → ∀ K v : ℝ, 0 < K → 0 < v →
    equilibrium g p e d K s v → 0 < (jac g p e d K s v).det →
      slopeK g p e d (v/s) (v/s*p (v/s)) s < 0

/-- Theorem 1: the first two statements, at a prescribed density in an open positive domain. -/
theorem pointwise_criterion {I : Set ℝ} (hI : IsOpen I) (hpos : I ⊆ Ioi 0)
    {s e d : ℝ} (hsi : s∈I) (he : 0<e) (hd : 0<d)
    {g : ℝ → ℝ} (hgC : ContDiffOn ℝ 2 g I)
    (hgp : ∀ x∈I, 0<g x) (hbp : ∀ x∈I, 0<deriv g x) :
    EveryTraceFalls g e d s ↔ 0 ≤ deriv (deriv (fun t => (g t)⁻¹)) s := by
  have hs : 0<s := hpos hsi
  have ha := hgp s hsi
  have hb := hbp s hsi
  have hder : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t := by
    filter_upwards [hI.mem_nhds hsi] with t ht
    exact ((hgC t ht).contDiffAt (hI.mem_nhds ht)).differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (deriv g) s := by
    have hn : ContDiffOn ℝ 1 (deriv g) I := hgC.deriv_of_isOpen hI (by norm_num)
    exact ((hn s hsi).contDiffAt (hI.mem_nhds hsi)).differentiableAt (by norm_num)
  rw [D1Core.reciprocal_curvature ha.ne' hder h₂, ← D1Core.criterion s (g s) (deriv g s) (deriv (deriv g) s) hs ha hb]
  constructor
  · intro H Q hQ hU
    let r := e*Q/d
    let p := holling e d r
    obtain ⟨hr,hK,heq,hl,had,eq,hdet⟩ :=
      realization he hd hs ha hb hder.self_of_nhds hQ hU
    have H' := H p had (cap g Q s) (r*s) hK (mul_pos hr hs) eq hdet
    have hρ : r*s/s = r := by field_simp
    change slopeK g p e d (r*s/s) (r*s/s * p (r*s/s)) s < 0 at H'
    rw [hρ, ← hl] at H'
    exact (slopeK_neg_iff hs ha (hU.trans (upper_lt hs ha hb)) ((upper_iff hs ha hb).mp hU)
      hder h₂ (intake_deriv had hr).1 heq hl).mp H'
  · intro H p hp K v hK hv hE hdet
    obtain ⟨hQ,hlt,hD,heq,_⟩ :=
      reduce_equilibrium hs hv he hK ha hder.self_of_nhds hp hE hdet
    apply (slopeK_neg_iff hs ha hlt hD hder h₂ (intake_deriv hp (div_pos hv hs)).1 heq rfl).mpr
    exact H _ hQ ((upper_iff hs ha hb).mpr hD)

/-- The inverse function theorem supplies a genuine local K-coordinate on the equilibrium
curve. `eqK` is the physical trace derivative as a HasDerivAt certificate, not a formal quotient. -/
theorem chart_trace_continuous {g p : ℝ → ℝ} {s e d r Q : ℝ}
    (hs : 0<s) (hr : 0<r) (ha : 0<g s) (hlt : Q<g s) (hD : 0<D g Q s)
    (hgc : ContDiffAt ℝ 2 g s)
    (h₁ : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t) (h₂ : DifferentiableAt ℝ (deriv g) s)
    (hp : DifferentiableAt ℝ p r) (he : e*p r=d) (hl : Q=r*p r) :
    ∃ X : ℝ → ℝ, X (cap g Q s) = s ∧ ContinuousAt X (cap g Q s) ∧
      (∀ᶠ k in 𝓝 (cap g Q s), 0<X k ∧ equilibrium g p e d k (X k) (r*X k)) ∧
      HasDerivAt (fun k => (jac g p e d k (X k) (r*X k)).trace)
        (slopeK g p e d r Q s) (cap g Q s) := by
  have hden : 0 < 1-Q/g s := sub_pos.mpr ((div_lt_one ha).mpr hlt)
  have hcap := capacity_deriv ha hlt h₁.self_of_nhds
  have hk : 0 < deriv (cap g Q) s := by rw [hcap.deriv]; positivity
  have hc : ContDiffAt ℝ 2 (cap g Q) s :=
    contDiffAt_id.div (contDiffAt_const.sub (contDiffAt_const.div hgc ha.ne')) hden.ne'
  have H := hc.hasStrictDerivAt (by norm_num)
  let X := H.localInverse _ _ _ hk.ne'
  have hX : X (cap g Q s)=s := (H.hasStrictFDerivAt_equiv hk.ne').localInverse_apply_image
  have invR : ∀ᶠ k in 𝓝 (cap g Q s), cap g Q (X k)=k :=
    (H.hasStrictFDerivAt_equiv hk.ne').eventually_right_inverse
  have dX : HasDerivAt X (deriv (cap g Q) s)⁻¹ (cap g Q s) := (H.to_localInverse (hf' := hk.ne')).hasDerivAt
  have tend : Tendsto X (𝓝 (cap g Q s)) (𝓝 s) := by simpa only [hX] using dX.continuousAt.tendsto
  refine ⟨X,hX,dX.continuousAt,?_,?_⟩
  · filter_upwards [invR, tend (Ioi_mem_nhds hs), tend (h₁.self_of_nhds.continuousAt.tendsto (Ioi_mem_nhds hlt)),
        tend (h₁.self_of_nhds.continuousAt.tendsto (Ioi_mem_nhds ha))] with k h₀ hx hq hg
    refine ⟨hx, (equilibrium_iff hx (mul_pos hr hx)).mpr ?_⟩
    change 0<X k at hx
    change 0<g (X k) at hg
    have hq' := q_cap hx.ne' hg.ne' hq
    rw [h₀] at hq'
    simp only [mul_div_cancel_right₀ _ hx.ne', hq', hl, he, and_self]
  · have hT := ray_deriv hs ha hlt h₁ h₂ hp he hl
    have dtrace : HasDerivAt (rayT g p e d r Q) (deriv (rayT g p e d r Q) s) (X (cap g Q s)) := by
      rw [hX]; exact hT.differentiableAt.hasDerivAt
    have HH := dtrace.comp (cap g Q s) dX
    apply HasDerivAt.congr_of_eventuallyEq (f:=rayT g p e d r Q ∘ X)
    · simpa [slopeK, div_eq_mul_inv,hX] using HH
    · filter_upwards [invR] with k hk'
      simp only [Function.comp_apply,rayT,hk']

theorem chart_trace {g p : ℝ → ℝ} {s e d r Q : ℝ}
    (hs : 0<s) (hr : 0<r) (ha : 0<g s) (hlt : Q<g s) (hD : 0<D g Q s)
    (hgc : ContDiffAt ℝ 2 g s)
    (h₁ : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t) (h₂ : DifferentiableAt ℝ (deriv g) s)
    (hp : DifferentiableAt ℝ p r) (he : e*p r=d) (hl : Q=r*p r) :
    ∃ X : ℝ → ℝ, X (cap g Q s) = s ∧
      (∀ᶠ k in 𝓝 (cap g Q s), 0<X k ∧ equilibrium g p e d k (X k) (r*X k)) ∧
      HasDerivAt (fun k => (jac g p e d k (X k) (r*X k)).trace)
        (slopeK g p e d r Q s) (cap g Q s) := by
  obtain ⟨X,hX,_,eq,hT⟩ := chart_trace_continuous hs hr ha hlt hD hgc h₁ h₂ hp he hl
  exact ⟨X,hX,eq,hT⟩

/-- Every positive Cartesian equilibrium near the reference point has the same intake ratio. -/
theorem equilibrium_coordinates {g p : ℝ → ℝ} {r e d k x y : ℝ}
    (hp : Admissible p) (hr : 0<r) (he : 0<e) (heq : e*p r=d)
    (hx : 0<x) (hy : 0<y) (hk : 0<k) (hg : 0<g x) (h : equilibrium g p e d k x y) :
    y = r*x ∧ cap g (r*p r) x = k := by
  obtain ⟨hq,hpval⟩ := (equilibrium_iff hx hy).mp h
  have hratio : y/x = r := hp.decreasing.injOn (div_pos hy hx) hr
    (mul_left_cancel₀ he.ne' (hpval.trans heq.symm))
  rw [hratio] at hq
  exact ⟨(div_eq_iff hx.ne').mp hratio,(capacity_of_q hk.ne' hx.ne' hg.ne' hq).symm⟩

/-- Any continuous branch of the two original equilibrium equations has this derivative. -/
theorem branch_trace {g p X Y : ℝ → ℝ} {e d K s v : ℝ} (he : 0<e) (hK : 0<K)
    (hs : 0<s) (hv : 0<v) (ha : 0<g s) (h₁ : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t)
    (h₂ : DifferentiableAt ℝ (deriv g) s) (hp : Admissible p)
    (eq : equilibrium g p e d K s v) (hdet : 0<(jac g p e d K s v).det)
    (hX : X K=s) (hY : Y K=v) (hcX : ContinuousAt X K) (hcY : ContinuousAt Y K)
    (hE : ∀ᶠ k in 𝓝 K, equilibrium g p e d k (X k) (Y k)) :
    HasDerivAt (fun k => (jac g p e d k (X k) (Y k)).trace)
      (slopeK g p e d (v/s) (v/s*p (v/s)) s) K := by
  let r := v/s
  let Q := r*p r
  have hr : 0<r := div_pos hv hs
  obtain ⟨_,hlt,hD,hbr,_⟩ := reduce_equilibrium hs hv he hK ha h₁.self_of_nhds hp eq hdet
  have tx : Tendsto X (𝓝 K) (𝓝 s) := by simpa only [hX] using hcX.tendsto
  have ty : Tendsto Y (𝓝 K) (𝓝 v) := by simpa only [hY] using hcY.tendsto
  have coords : ∀ᶠ k in 𝓝 K, Y k=r*X k ∧ cap g Q (X k)=k := by
    filter_upwards [hE, Ioi_mem_nhds hK, tx (Ioi_mem_nhds hs), ty (Ioi_mem_nhds hv),
      tx (h₁.self_of_nhds.continuousAt.tendsto (Ioi_mem_nhds ha))] with k hh hk hx hy hg
    exact equilibrium_coordinates hp hr he hbr hx hy hk hg hh
  have hk := capacity_deriv ha hlt h₁.self_of_nhds
  have hden : 0 < 1-Q/g s := sub_pos.mpr ((div_lt_one ha).mpr hlt)
  have hkpos : 0 < deriv (cap g Q) s := by rw [hk.deriv]; positivity
  have dK : HasDerivAt (cap g Q) (deriv (cap g Q) s) (X K) := by
    rw [hX]; exact hk.differentiableAt.hasDerivAt
  have dX := HasDerivAt.of_local_left_inverse hcX dK hkpos.ne' (coords.mono fun _ h => h.2)
  have dT : HasDerivAt (rayT g p e d r Q) (deriv (rayT g p e d r Q) s) (X K) := by
    rw [hX]; exact (ray_deriv hs ha hlt h₁ h₂ (intake_deriv hp hr).1 hbr rfl).differentiableAt.hasDerivAt
  apply HasDerivAt.congr_of_eventuallyEq (f:=rayT g p e d r Q ∘ X)
  · simpa only [slopeK,div_eq_mul_inv] using dT.comp K dX
  · filter_upwards [coords] with k h
    simp only [Function.comp_apply,rayT,h.1,h.2]

/-- A physical enrichment derivative means differentiating the actual Cartesian trace
along any continuous graph satisfying the equilibrium equations for nearby K. -/
def PhysicalTraceFalls (g : ℝ → ℝ) (e d s : ℝ) : Prop :=
  ∀ p : ℝ → ℝ, Admissible p → ∀ K v : ℝ, 0<K → 0<v →
    equilibrium g p e d K s v → 0<(jac g p e d K s v).det →
    ∀ X Y : ℝ → ℝ, X K=s → Y K=v → ContinuousAt X K → ContinuousAt Y K →
      (∀ᶠ k in 𝓝 K, equilibrium g p e d k (X k) (Y k)) →
        deriv (fun k => (jac g p e d k (X k) (Y k)).trace) K < 0

theorem physical_criterion {I : Set ℝ} (hI : IsOpen I) (hpos : I ⊆ Ioi 0)
    {s e d : ℝ} (hsi : s∈I) (he : 0<e) (hd : 0<d)
    {g : ℝ → ℝ} (hgC : ContDiffOn ℝ 2 g I)
    (hgp : ∀ x∈I, 0<g x) (hbp : ∀ x∈I, 0<deriv g x) :
    PhysicalTraceFalls g e d s ↔ 0 ≤ deriv (deriv (fun t => (g t)⁻¹)) s := by
  have hs : 0<s := hpos hsi
  have ha := hgp s hsi
  have hder : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t := by
    filter_upwards [hI.mem_nhds hsi] with t ht
    exact (hgC.contDiffAt (hI.mem_nhds ht)).differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (deriv g) s :=
    ((hgC.deriv_of_isOpen hI (m:=1) (by norm_num)).contDiffAt (hI.mem_nhds hsi)).differentiableAt (by norm_num)
  rw [←pointwise_criterion hI hpos hsi he hd hgC hgp hbp]
  constructor
  · intro H p hp K v hK hv eq hdet
    let r := v/s
    let Q := r*p r
    have hr : 0<r := div_pos hv hs
    obtain ⟨_,hlt,hD,hbr,hcap⟩ := reduce_equilibrium hs hv he hK ha hder.self_of_nhds hp eq hdet
    obtain ⟨X,hX,hcX,hE,hT⟩ := chart_trace_continuous hs hr ha hlt hD (hgC.contDiffAt (hI.mem_nhds hsi))
      hder h₂ (intake_deriv hp hr).1 hbr rfl
    change K=cap g Q s at hcap
    rw [←hcap] at hX hcX hE hT
    have hy : r*X K=v := by rw [hX]; exact div_mul_cancel₀ _ hs.ne'
    have hh := H p hp K v hK hv eq hdet X (fun k => r*X k) hX hy hcX (continuousAt_const.mul hcX)
      (hE.mono fun _ h => h.2)
    exact hT.deriv ▸ hh
  · intro H p hp K v hK hv eq hdet X Y hX hY hcX hcY hE
    rw [(branch_trace he hK hs hv ha hder h₂ hp eq hdet hX hY hcX hcY hE).deriv]
    exact H p hp K v hK hv eq hdet

/-- Explicit regular Holling II realization, including a K-parameterized physical trace. -/
def HollingSlope (g : ℝ → ℝ) (e d s Q t : ℝ) : Prop :=
  let r := e*Q/d
  let p := holling e d r
  let K := cap g Q s
  0<r ∧ 0<K ∧ Admissible p ∧ equilibrium g p e d K s (r*s) ∧ 0<(jac g p e d K s (r*s)).det ∧
  ∃ X : ℝ → ℝ, X K=s ∧ ContinuousAt X K ∧
    (∀ᶠ k in 𝓝 K, 0<X k ∧ equilibrium g p e d k (X k) (r*X k)) ∧
    HasDerivAt (fun k => (jac g p e d k (X k) (r*X k)).trace) t K

theorem holling_slope {g : ℝ → ℝ} {e d s Q : ℝ} (he : 0<e) (hd : 0<d)
    (hs : 0<s) (ha : 0<g s) (hb : 0<deriv g s) (hgc : ContDiffAt ℝ 2 g s)
    (h₁ : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t) (h₂ : DifferentiableAt ℝ (deriv g) s)
    (hQ : 0<Q) (hU : Q < D1Core.upper s (g s) (deriv g s)) :
    ∃ t v : ℝ, HollingSlope g e d s Q t ∧ 0<v ∧
      t=(Q*D1Core.elasticityPrime s (g s) (deriv g s) (deriv (deriv g) s)-deriv g s)/v := by
  let r := e*Q/d
  let p := holling e d r
  obtain ⟨hr,hK,heq,hl,had,eq,hdet⟩ := realization he hd hs ha hb h₁.self_of_nhds hQ hU
  have hlt := hU.trans (upper_lt hs ha hb)
  have hD := (upper_iff hs ha hb).mp hU
  have hp := (intake_deriv had hr).1
  obtain ⟨X,hX,hc,hE,hT⟩ := chart_trace_continuous hs hr ha hlt hD hgc h₁ h₂ hp heq hl
  refine ⟨slopeK g p e d r Q s, deriv (cap g Q) s, ⟨hr,hK,had,eq,hdet,X,hX,hc,hE,hT⟩,?_,?_⟩
  · have hden : 0<1-Q/g s := sub_pos.mpr ((div_lt_one ha).mpr hlt)
    rw [(capacity_deriv ha hlt h₁.self_of_nhds).deriv]; positivity
  · unfold slopeK
    rw [(ray_deriv hs ha hlt h₁ h₂ hp heq hl).deriv]

/-- The final clause of Theorem 1, with three exact physical equilibrium witnesses. -/
theorem negative_curvature_three_holling_signs {I : Set ℝ} (hI : IsOpen I) (hpos : I ⊆ Ioi 0)
    {s e d : ℝ} (hsi : s∈I) (he : 0<e) (hd : 0<d)
    {g : ℝ → ℝ} (hgC : ContDiffOn ℝ 2 g I)
    (hgp : ∀ x∈I, 0<g x) (hbp : ∀ x∈I, 0<deriv g x)
    (hcurv : deriv (deriv (fun t => (g t)⁻¹)) s < 0) :
    ∃ q₁ q₂ q₃ t₁ t₂ t₃ : ℝ, 0<q₁ ∧ q₁<q₂ ∧ q₂<q₃ ∧ q₃<D1Core.upper s (g s) (deriv g s) ∧
    HollingSlope g e d s q₁ t₁ ∧ HollingSlope g e d s q₂ t₂ ∧ HollingSlope g e d s q₃ t₃ ∧
    t₁<0 ∧ t₂=0 ∧ 0<t₃ := by
  have hs : 0<s := hpos hsi
  have ha := hgp s hsi
  have hb := hbp s hsi
  have hder : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ g t := by
    filter_upwards [hI.mem_nhds hsi] with t ht
    exact (hgC.contDiffAt (hI.mem_nhds ht)).differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (deriv g) s :=
    ((hgC.deriv_of_isOpen hI (m:=1) (by norm_num)).contDiffAt (hI.mem_nhds hsi)).differentiableAt (by norm_num)
  rw [D1Core.reciprocal_curvature ha.ne' hder h₂] at hcurv
  obtain ⟨q₁,q₂,q₃,h₁,h₁₂,h₂₃,h₃,hn,hz,hp⟩ := D1Core.all_signs _ _ _ _ hs ha hb hcurv
  have H := @holling_slope g e d s
  have hgc := hgC.contDiffAt (hI.mem_nhds hsi)
  obtain ⟨t₁,v₁,H₁,hv₁,eq₁⟩ := H (Q:=q₁) he hd hs ha hb hgc hder h₂ h₁ ((h₁₂.trans h₂₃).trans h₃)
  obtain ⟨t₂,v₂,H₂,hv₂,eq₂⟩ := H (Q:=q₂) he hd hs ha hb hgc hder h₂ (h₁.trans h₁₂) (h₂₃.trans h₃)
  obtain ⟨t₃,v₃,H₃,hv₃,eq₃⟩ := H (Q:=q₃) he hd hs ha hb hgc hder h₂ ((h₁.trans h₁₂).trans h₂₃) h₃
  exact ⟨q₁,q₂,q₃,t₁,t₂,t₃,h₁,h₁₂,h₂₃,h₃,H₁,H₂,H₃,eq₁ ▸ div_neg_of_neg_of_pos hn hv₁,
    by rw [eq₂,hz,zero_div],eq₃ ▸ div_pos hp hv₃⟩

#print axioms branch_trace
#print axioms physical_criterion
#print axioms negative_curvature_three_holling_signs
#print axioms jac_on_ray
#print axioms trace_det
#print axioms ray_deriv
#print axioms realization
#print axioms chart_trace
#print axioms pointwise_criterion
end Direction1
