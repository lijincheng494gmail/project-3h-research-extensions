import Direction2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! Direction 2, competition-response supplement. A positive equilibrium at zero competition
with positive determinant gives an actual local branch. The proof eliminates the predator
coordinate and applies the one-dimensional inverse function theorem to competition as a
function of prey density. The only growth regularity hypothesis is local C¹.
Source: COMPETITION_ORDERING_THEOREM.tex, sections 2–4, starting-root continuation,
Theorems 1–2, and the chart in equation (3). -/
noncomputable section
open Set Filter
open scoped Topology
namespace Direction2
namespace Params

/-- Construction of a regular positive graph on a nontrivial competition interval.
The starting root, its determinant, and local C¹ growth are the input data. -/
theorem exists_local_branch (p : Params) {g : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hx : 0 < x₀) (hy : 0 < y₀) (r : p.Root g 0 x₀ y₀)
    (reg : 0 < p.detJ g 0 x₀ y₀) (hg : ContDiffAt ℝ 1 g x₀) :
    ∃ H > 0, ∃ b : p.Branch g H, b.x 0 = x₀ ∧ b.y 0 = y₀ ∧
      (∀ h ∈ Icc 0 H, ContDiffAt ℝ 1 b.x h ∧ ContDiffAt ℝ 1 b.y h) ∧
      (∀ᶠ u in 𝓝 x₀, ∀ h v : ℝ, 0 < v → p.Root g h u v → u = b.x h ∧ v = b.y h) := by
  let Y := fun x => p.β*g x/(p.m-g x)
  let N := fun x => p.e*x*(p.m-g x)/p.β-p.d
  let F := fun x => N x / Y x
  have nb := (add_pos p.hβ hy).ne'
  have base : p.e*p.m*x₀ = (p.β+y₀)*p.d := by simpa using r.2
  have gm : p.m-g x₀ = p.m*p.β/(p.β+y₀) := by
    apply (eq_div_iff nb).2
    linear_combination -r.1
  have gap : 0 < p.m-g x₀ := by rw [gm]; exact div_pos (mul_pos p.hm p.hβ) (add_pos p.hβ hy)
  have y0 : Y x₀ = y₀ := by
    apply (div_eq_iff gap.ne').2
    linear_combination r.1
  have n0 : N x₀ = 0 := by
    change p.e*x₀*(p.m-g x₀)/p.β-p.d=0
    rw [gm]
    have tmp : p.e*x₀*(p.m*p.β/(p.β+y₀))/p.β=p.e*p.m*x₀/(p.β+y₀) := by
      field_simp [p.hβ.ne',nb]; ring
    rw [tmp, (div_eq_iff nb).2 (by linarith only [base] : p.e*p.m*x₀ = p.d*(p.β+y₀)), sub_self]
  have f0 : F x₀ = 0 := by simp [F,n0]
  have d : 0 < p.scaledDet g 0 x₀ y₀ := by
    rw [p.determinant_eq r hy] at reg
    exact pos_of_mul_pos_right reg (div_nonneg (mul_nonneg hx.le hy.le) (sq_nonneg _))
  have idD : p.scaledDet g 0 x₀ y₀ = (p.e*p.m)*((p.m-g x₀)-x₀*deriv g x₀) := by
    simp only [scaledDet,zero_mul,add_zero]
    linear_combination deriv g x₀ * base
  rw [idD] at d
  have pos := pos_of_mul_pos_right d (mul_pos p.he p.hm).le
  have cy : ContDiffAt ℝ 1 Y x₀ :=
    (contDiffAt_const.mul hg).div (contDiffAt_const.sub hg) gap.ne'
  have cn : ContDiffAt ℝ 1 N x₀ :=
    (((contDiffAt_const.mul contDiffAt_id).mul (contDiffAt_const.sub hg)).div
      contDiffAt_const p.hβ.ne').sub contDiffAt_const
  have yne : Y x₀ ≠ 0 := by rw [y0]; exact hy.ne'
  have cg : ContDiffAt ℝ 1 F x₀ := cn.div cy yne
  have dg := (hg.differentiableAt le_rfl).hasDerivAt
  have dn : HasDerivAt N (p.e*((p.m-g x₀)-x₀*deriv g x₀)/p.β) x₀ := by
    convert (((((hasDerivAt_id x₀).const_mul p.e).mul
      ((hasDerivAt_const x₀ p.m).sub dg)).div_const p.β).sub_const p.d) using 1
    dsimp; ring
  have df := (dn.div (cy.differentiableAt le_rfl).hasDerivAt yne).deriv
  change deriv F x₀ = _ at df
  rw [y0,n0] at df
  have dfpos : 0 < deriv F x₀ := by
    rw [df,zero_mul,sub_zero]
    exact div_pos (mul_pos (div_pos (mul_pos p.he pos) p.hβ) hy) (sq_pos_of_pos hy)
  have strict := cg.hasStrictDerivAt le_rfl
  let e := (strict.hasStrictFDerivAt_equiv dfpos.ne').toPartialHomeomorph F
  let X : ℝ → ℝ := e.symm
  have mem : x₀ ∈ e.source := (strict.hasStrictFDerivAt_equiv dfpos.ne').mem_toPartialHomeomorph_source
  have ez : e x₀ = 0 := f0
  have mt : (0:ℝ) ∈ e.target := ez ▸ e.map_source mem
  have x0 : X 0 = x₀ := by rw [←ez]; exact e.left_inv mem
  have invSmooth : ContDiffAt ℝ 1 X 0 := by
    apply e.contDiffAt_symm_deriv dfpos.ne' mt
    · change HasDerivAt F (deriv F x₀) (X 0)
      rw [x0]
      exact strict.hasDerivAt
    · change ContDiffAt ℝ 1 F (X 0)
      rwa [x0]
  have lim : Tendsto X (𝓝 0) (𝓝 x₀) := by simpa only [← x0] using (e.continuousAt_symm mt).tendsto
  have y0' : Y (X 0)=y₀ := x0 ▸ y0
  have limY := cy.continuousAt.tendsto.comp lim
  rw [y0] at limY
  have ader : ContinuousAt (deriv g) x₀ :=
    ((hg.fderiv_right (m:=0) (by norm_num)).clm_apply (g := fun _ : ℝ => (1:ℝ)) contDiffAt_const).continuousAt
  have limg := hg.continuousAt.tendsto.comp lim
  have limD : Tendsto (fun h => p.scaledDet g h (X h) (Y (X h))) (𝓝 0)
      (𝓝 (p.scaledDet g 0 x₀ y₀)) := by
    unfold scaledDet
    exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub limg)).sub
      (((tendsto_const_nhds.add (tendsto_id.mul (tendsto_const_nhds.add
        (tendsto_const_nhds.mul limY)))).mul (tendsto_const_nhds.add limY)).mul
          (ader.tendsto.comp lim))
  have here : 0 < p.scaledDet g 0 x₀ y₀ := idD.symm ▸ d
  have good : ∀ᶠ h in 𝓝 (0:ℝ), h ∈ e.target ∧ 0 < X h ∧ 0 < Y (X h) ∧
      0 < p.m-g (X h) ∧ 0 < p.scaledDet g h (X h) (Y (X h)) ∧ ContDiffAt ℝ 1 g (X h) := by
    filter_upwards [e.open_target.mem_nhds mt, lim (Ioi_mem_nhds hx), limY (Ioi_mem_nhds hy),
      (tendsto_const_nhds.sub limg) (Ioi_mem_nhds gap), limD (Ioi_mem_nhds here),
      lim (hg.eventually (by simp))] with h ht px py pg pd diff using ⟨ht,px,py,pg,pd,diff⟩
  obtain ⟨H,hH,both⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp
    (nhdsWithin_le_nhds (good.and (invSmooth.eventually (by simp))))
  have sub {h : ℝ} (hh : h ∈ Icc 0 H) := (both hh).1
  have root : ∀ h ∈ Icc 0 H, p.Root g h (X h) (Y (X h)) := by
    intro h hh
    obtain ⟨ht,_,py,pg,_,_⟩ := sub hh
    have inv : F (X h)=h := e.right_inv ht
    let x := X h
    let y := Y x
    have ym : y*(p.m-g x)=p.β*g x := (div_eq_iff pg.ne').1 (show p.β*g x/(p.m-g x) = y from rfl) |>.symm
    have eq1 : g x*(p.β+y)=p.m*y := by linear_combination -ym
    have eqb : (p.β+y)*(p.m-g x) = p.β*p.m := by linear_combination ym
    have eqn : p.e*x*(p.m-g x)=(p.d+h*y)*p.β := by
      have v : p.e*x*(p.m-g x)/p.β-p.d = h*y := (div_eq_iff py.ne').1 inv
      apply (div_eq_iff p.hβ.ne').1
      linarith only [v]
    refine ⟨eq1,?_⟩
    apply mul_left_cancel₀ p.hβ.ne'
    change p.β*(p.e*p.m*x) = p.β*((p.β+y)*(p.d+h*y))
    linear_combination (p.β+y)*eqn - p.e*x*eqb
  have uniq : ∀ᶠ u in 𝓝 x₀, ∀ h v : ℝ, 0 < v → p.Root g h u v →
      u = X h ∧ v = Y (X h) := by
    filter_upwards [e.open_source.mem_nhds mem, (tendsto_const_nhds.sub hg.continuousAt.tendsto)
      (Ioi_mem_nhds gap)] with u hu un
    intro h v hv rootuv
    have pg : 0<p.m-g u := un
    have yv : Y u = v := (div_eq_iff pg.ne').2 (by linear_combination rootuv.1)
    have vden := (add_pos p.hβ hv).ne'
    have fact : (p.m-g u)*(p.β+v)=p.m*p.β := by linear_combination -rootuv.1
    have num : p.e*u*(p.m-g u) = (p.d+h*v)*p.β := by
      apply mul_right_cancel₀ vden
      linear_combination p.β*rootuv.2 + (p.e*u)*fact
    have xy : F u = h := by
      change (p.e*u*(p.m-g u)/p.β-p.d)/Y u=h
      rw [yv,(div_eq_iff p.hβ.ne').2 num]
      apply (div_eq_iff hv.ne').2
      ring
    have ux : u=X h := by rw [←xy]; exact (e.left_inv hu).symm
    exact ⟨ux,by rw [←ux,yv]⟩
  have cx : ContinuousOn X (Icc 0 H) := e.continuousOn_symm.mono (fun h hh => (sub hh).1)
  refine ⟨H,hH,⟨X,fun h => Y (X h),cx,?_,?_,?_,root,?_,?_⟩,x0,y0',?_,uniq⟩
  · intro h hh
    obtain ⟨_,_,_,pg,_,diff⟩ := sub hh
    exact (((continuousAt_const.mul diff.continuousAt).div (continuousAt_const.sub diff.continuousAt)
      pg.ne').comp_continuousWithinAt (cx h hh))
  · exact fun h hh => (sub hh).2.1
  · exact fun h hh => (sub hh).2.2.1
  · intro h hh
    obtain ⟨_,px,py,_,pd,_⟩ := sub hh
    rw [p.determinant_eq (root h hh) py]
    exact mul_pos (div_pos (mul_pos px py) (sq_pos_of_pos (add_pos p.hβ py))) pd
  · exact fun h hh => (sub hh).2.2.2.2.2.differentiableAt le_rfl
  · intro h hh
    obtain ⟨_,_,_,pg,_,diff⟩ := sub hh
    have sx := (both hh).2
    exact ⟨sx, ((contDiffAt_const.mul diff).div (contDiffAt_const.sub diff) pg.ne').comp h sx⟩

private def Branch.shorten {p : Params} {g : ℝ → ℝ} {H H' : ℝ}
    (b : p.Branch g H) (le : H' ≤ H) : p.Branch g H' where
  x := b.x
  y := b.y
  cx := b.cx.mono (Icc_subset_Icc_right le)
  cy := b.cy.mono (Icc_subset_Icc_right le)
  posX := fun h hh => b.posX h (Icc_subset_Icc_right le hh)
  posY := fun h hh => b.posY h (Icc_subset_Icc_right le hh)
  root := fun h hh => b.root h (Icc_subset_Icc_right le hh)
  regular := fun h hh => b.regular h (Icc_subset_Icc_right le hh)
  smooth := fun h hh => b.smooth h (Icc_subset_Icc_right le hh)

end Params
namespace Calibration

/-- From three positive determinants at the shared calibrated root, construct all
three branches on one positive interval and order their right sensitivities and states. -/
theorem exists_three_ordered_branches {p : Params} (c : Calibration p)
    (hL : 0 < p.detJ (c.growth 0) 0 c.x₀ c.y₀)
    (hW : 0 < p.detJ (c.growth c.weakS) 0 c.x₀ c.y₀)
    (hS : 0 < p.detJ (c.growth c.strongS) 0 c.x₀ c.y₀) :
    ∃ H > 0, ∃ (L : p.Branch (c.growth 0) H) (W : p.Branch (c.growth c.weakS) H)
        (S : p.Branch (c.growth c.strongS) H),
      (L.x 0=c.x₀ ∧ W.x 0=c.x₀ ∧ S.x 0=c.x₀ ∧ L.y 0=c.y₀ ∧ W.y 0=c.y₀ ∧ S.y 0=c.y₀) ∧
      (derivWithin L.y (Icc 0 H) 0 < derivWithin W.y (Icc 0 H) 0 ∧
        derivWithin W.y (Icc 0 H) 0 < derivWithin S.y (Icc 0 H) 0) ∧
      (∀ h ∈ Ioc 0 H, c.x₀ < L.x h ∧ L.x h < W.x h ∧ W.x h < S.x h ∧
        L.y h < W.y h ∧ W.y h < S.y h) := by
  have make (s : ℝ) (reg : 0 < p.detJ (c.growth s) 0 c.x₀ c.y₀) :=
    p.exists_local_branch (c.posA.trans c.left) c.posY (c.matched_root s) reg
      (show ContDiffAt ℝ 1 (c.growth s) c.x₀ from
        (contDiffAt_const.mul ((contDiffAt_const.sub contDiffAt_id).div_const _)).mul
          (contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_id.sub contDiffAt_const))))
  obtain ⟨Hl,hl,L,lx,ly,_,_⟩ := make 0 hL
  obtain ⟨Hw,hw,W,wx,wy,_,_⟩ := make c.weakS hW
  obtain ⟨Hs,hs,S,sx,sy,_,_⟩ := make c.strongS hS
  let H := min Hl (min Hw Hs)
  have hp : 0<H := lt_min hl (lt_min hw hs)
  let BL := L.shorten (H':=H) (min_le_left _ _)
  let BW := W.shorten (H':=H) ((min_le_right _ _).trans (min_le_left _ _))
  let BS := S.shorten (H':=H) ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨H,hp,BL,BW,BS,⟨lx,wx,sx,ly,wy,sy⟩,
    c.branch_local_order hp BL BW BS lx wx sx ly wy sy,
    c.three_model_finite_order hp BL BW BS lx wx sx ly wy sy⟩

end Calibration
end Direction2
#print axioms Direction2.Params.exists_local_branch
#print axioms Direction2.Calibration.exists_three_ordered_branches
