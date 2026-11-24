import Direction2

noncomputable section
open Set Filter
open scoped Topology
namespace Direction2.Feeding
variable (f : Feeding)

/-- The determinant of the two cleared equilibrium residuals for the common
feeding family. The ODE determinant has the positive factor x*y/denom². -/
def regularDet (g : ℝ → ℝ) (t x y : ℝ) :=
  (f.e*f.a-f.b*(f.d+t*y))*(f.a-f.c*g x) -
  (f.c*(f.d+t*y)+t*f.denom x y)*(deriv g x*f.denom x y+f.b*g x)

theorem root_cleared {g : ℝ → ℝ} {t x y : ℝ} (hx : 0<x) (hy : 0<y)
    (r : f.Root g t x y) :
    g x * f.denom x y = f.a*y ∧ f.e*f.a*x=(f.d+t*y)*f.denom x y :=
  ⟨(eq_div_iff (f.denom_pos hx.le hy.le).ne').1 r.1,
   (div_eq_iff (f.denom_pos hx.le hy.le).ne').1 r.2⟩

/-- Cleared ODE components multiplied by their positive coordinate factors. -/
def preyField (g : ℝ → ℝ) (x y : ℝ) := x/f.denom x y * (g x*f.denom x y-f.a*y)
def predatorField (t x y : ℝ) := y/f.denom x y * (f.e*f.a*x-(f.d+t*y)*f.denom x y)

theorem original_fields (g : ℝ → ℝ) (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    f.preyField g x y = x*g x-f.a*x*y/f.denom x y ∧
    f.predatorField t x y = f.e*(f.a*x*y/f.denom x y)-f.d*y-t*y^2 := by
  have n := (f.denom_pos hx.le hy.le).ne'
  unfold preyField predatorField
  constructor <;> field_simp [n] <;> ring

/-- The cleared-residual determinant has the same sign as the Cartesian
Jacobian of the full ODE at every positive differentiable root. -/
theorem cartesian_det (g : ℝ → ℝ) (t x y : ℝ) (hx : 0<x) (hy : 0<y)
    (hg : DifferentiableAt ℝ g x) (rt : f.Root g t x y) :
    deriv (fun u => f.preyField g u y) x * deriv (fun v => f.predatorField t x v) y -
    deriv (fun v => f.preyField g x v) y * deriv (fun u => f.predatorField t u y) x =
    x*y/(f.denom x y)^2 * f.regularDet g t x y := by
  have n := (f.denom_pos hx.le hy.le).ne'
  obtain ⟨gc,pc⟩ := f.root_cleared hx hy rt
  have eqg := sub_eq_zero.mpr gc
  have eqp := sub_eq_zero.mpr pc
  have i : HasDerivAt (fun u : ℝ => u) 1 x := hasDerivAt_id x
  have j : HasDerivAt (fun v : ℝ => v) 1 y := hasDerivAt_id y
  have dx : HasDerivAt (fun u => f.denom u y) f.b x := by
    simpa [denom] using (((i.const_mul f.b).const_add 1).add_const (f.c*y))
  have dy : HasDerivAt (fun v => f.denom x v) f.c y := by
    simpa [denom] using ((j.const_mul f.c).const_add (1+f.b*x))
  have xx := ((i.div dx n).mul ((hg.hasDerivAt.mul dx).sub_const (f.a*y))).deriv
  have xy := (((hasDerivAt_const y x).div dy n).mul
    ((dy.const_mul (g x)).sub (j.const_mul f.a))).deriv
  have yx := (((hasDerivAt_const x y).div dx n).mul
    ((i.const_mul (f.e*f.a)).sub (dx.const_mul (f.d+t*y)))).deriv
  have yy := ((j.div dy n).mul ((hasDerivAt_const y (f.e*f.a*x)).sub
    (((j.const_mul t).const_add f.d).mul dy))).deriv
  change deriv (fun u => f.preyField g u y) x = _ at xx
  change deriv (fun v => f.preyField g x v) y = _ at xy
  change deriv (fun u => f.predatorField t u y) x = _ at yx
  change deriv (fun v => f.predatorField t x v) y = _ at yy
  rw [xx,xy,yx,yy]
  simp only [eqg,eqp,mul_zero,zero_add]
  unfold regularDet
  field_simp [n]
  ring

/-- A positive determinant gives rightward motion directly from the two
undifferentiated branch equations. -/
theorem family_prey_strictMono {g x y : ℝ → ℝ} {H : ℝ}
    (cx : ContinuousOn x (Icc 0 H)) (cy : ContinuousOn y (Icc 0 H))
    (r : ∀ t ∈ Icc 0 H, 0 < x t ∧ 0 < y t ∧ f.Root g t (x t) (y t))
    (dg : ∀ t ∈ Icc 0 H, DifferentiableAt ℝ g (x t))
    (reg : ∀ t ∈ Icc 0 H, 0 < f.regularDet g t (x t) (y t)) :
    StrictMonoOn x (Icc 0 H) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 H) cx
  intro t ht
  have ht' := interior_subset ht
  let S := Icc 0 H
  let A := S \ {t}
  let v := f.a-f.c*g (x t)
  let T := fun z => f.d+z*y z
  let Z := fun z => f.denom (x z) (y z)
  let u := fun z => dslope g (x t) (x z)*Z z+f.b*g (x t)
  let W := fun z => f.c*T z+z*Z t
  let V := fun z => f.e*f.a-f.b*T z
  let D := fun z => V z*v-W z*u z
  have sc : A ⊆ S := diff_subset
  obtain ⟨xt,yt,rt⟩ := r t ht'
  obtain ⟨g0,p0⟩ := f.root_cleared xt yt rt
  have dz : 0 < D t := by simpa [D,V,v,W,T,u,Z,regularDet] using reg t ht'
  have cz : ContinuousWithinAt Z S t := (continuousWithinAt_const.add
    ((cx t ht').const_mul f.b)).add ((cy t ht').const_mul f.c)
  have ct : ContinuousWithinAt T S t := continuousWithinAt_const.add
    (continuousWithinAt_id.mul (cy t ht'))
  have cu : ContinuousWithinAt u S t := (((continuousAt_dslope_same.mpr
    (dg t ht')).comp_continuousWithinAt (cx t ht')).mul cz).add continuousWithinAt_const
  have cw : ContinuousWithinAt W S t := (ct.const_mul f.c).add
    (continuousWithinAt_id.mul continuousWithinAt_const)
  have cv : ContinuousWithinAt V S t := continuousWithinAt_const.sub (ct.const_mul f.b)
  have cd : ContinuousWithinAt D S t := (cv.mul continuousWithinAt_const).sub (cw.mul cu)
  have den := ((cd.mono sc).tendsto.eventually (eventually_ne_nhds dz.ne'))
  have eqs : ∀ᶠ z in 𝓝[A] t, slope x t z = v*(y t*Z t)/D z := by
    filter_upwards [self_mem_nhdsWithin,den] with z hz nz
    have hs : z ∈ S := hz.1
    have nt : z ≠ t := hz.2
    obtain ⟨ax,ay,rz⟩ := r z hs
    obtain ⟨ge,pe⟩ := f.root_cleared ax ay rz
    have sec := sub_smul_dslope g (x t) (x z)
    rw [smul_eq_mul] at sec
    have E1 : u z*(x z-x t) = v*(y z-y t) := by
      dsimp [u,v,Z,denom]
      dsimp [denom] at ge g0
      linear_combination (1+f.b*x z+f.c*y z)*sec + ge - g0
    have E2 : V z*(x z-x t) = W z*(y z-y t)+(z-t)*(y t*Z t) := by
      dsimp [V,W,T,Z,denom]
      dsimp [denom] at pe p0
      linear_combination pe-p0
    rw [slope_def_field]
    apply (div_eq_div_iff (sub_ne_zero.mpr nt) nz).2
    dsimp only [D]
    linear_combination v*E2-W z*E1
  have der : HasDerivWithinAt x (v*(y t*Z t)/D t) S t :=
    hasDerivWithinAt_iff_tendsto_slope.mpr
      ((tendsto_const_nhds.div (cd.mono sc).tendsto dz.ne').congr' (eqs.mono fun _ e => e.symm))
  rw [(der.hasDerivAt (mem_interior_iff_mem_nhds.mp ht)).deriv]
  have zpos : 0 < Z t := f.denom_pos xt.le yt.le
  have vpos : 0 < v := by
    have eq : Z t * v = f.a*(1+f.b*x t) := by
      dsimp [Z,v,denom]
      dsimp [denom] at g0
      linear_combination -f.c*g0
    exact pos_of_mul_pos_right (eq ▸ mul_pos f.ha (by linarith [mul_nonneg f.hb xt.le])) zpos.le
  exact div_pos (mul_pos vpos (mul_pos yt zpos)) dz

theorem four_law_regular_order {g₁ g₂ x₁ x₂ y₁ y₂ : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (cx₁ : ContinuousOn x₁ (Icc 0 H))
    (cx₂ : ContinuousOn x₂ (Icc 0 H)) (cy₂ : ContinuousOn y₂ (Icc 0 H))
    (startX : x₁ 0 = x₂ 0) (startY : y₁ 0 = y₂ 0)
    (r₁ : ∀ t ∈ Icc 0 H, 0 < x₁ t ∧ 0 < y₁ t ∧ f.Root g₁ t (x₁ t) (y₁ t))
    (r₂ : ∀ t ∈ Icc 0 H, 0 < x₂ t ∧ 0 < y₂ t ∧ f.Root g₂ t (x₂ t) (y₂ t))
    (dg : ∀ t ∈ Icc 0 H, DifferentiableAt ℝ g₂ (x₂ t))
    (reg : ∀ t ∈ Icc 0 H, 0 < f.regularDet g₂ t (x₂ t) (y₂ t))
    (gap : ∀ h ∈ Ioc 0 H, x₂ 0 < x₂ h → g₁ (x₂ h) < g₂ (x₂ h)) :
    ∀ h ∈ Ioc 0 H, x₁ h < x₂ h ∧ y₁ h < y₂ h := by
  apply f.four_law_order hH cx₁ startX startY r₁ r₂ _ gap
  intro h hh
  exact f.family_prey_strictMono cx₂ cy₂ r₂ dg reg ⟨le_rfl,hH.le⟩ ⟨hh.1.le,hh.2⟩ hh.1

theorem four_law_cartesian_order {g₁ g₂ x₁ x₂ y₁ y₂ : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (cx₁ : ContinuousOn x₁ (Icc 0 H))
    (cx₂ : ContinuousOn x₂ (Icc 0 H)) (cy₂ : ContinuousOn y₂ (Icc 0 H))
    (startX : x₁ 0 = x₂ 0) (startY : y₁ 0 = y₂ 0)
    (r₁ : ∀ t ∈ Icc 0 H, 0 < x₁ t ∧ 0 < y₁ t ∧ f.Root g₁ t (x₁ t) (y₁ t))
    (r₂ : ∀ t ∈ Icc 0 H, 0 < x₂ t ∧ 0 < y₂ t ∧ f.Root g₂ t (x₂ t) (y₂ t))
    (dg : ∀ t ∈ Icc 0 H, DifferentiableAt ℝ g₂ (x₂ t))
    (det : ∀ t ∈ Icc 0 H,
      0 < deriv (fun u => f.preyField g₂ u (y₂ t)) (x₂ t) *
            deriv (fun v => f.predatorField t (x₂ t) v) (y₂ t) -
          deriv (fun v => f.preyField g₂ (x₂ t) v) (y₂ t) *
            deriv (fun u => f.predatorField t u (y₂ t)) (x₂ t))
    (gap : ∀ h ∈ Ioc 0 H, x₂ 0 < x₂ h → g₁ (x₂ h) < g₂ (x₂ h)) :
    ∀ h ∈ Ioc 0 H, x₁ h < x₂ h ∧ y₁ h < y₂ h := by
  apply f.four_law_regular_order hH cx₁ cx₂ cy₂ startX startY r₁ r₂ dg _ gap
  intro t ht
  obtain ⟨hx,hy,rt⟩ := r₂ t ht
  have positive := det t ht
  rw [f.cartesian_det g₂ t (x₂ t) (y₂ t) hx hy (dg t ht) rt] at positive
  exact pos_of_mul_pos_right positive (div_nonneg (mul_nonneg hx.le hy.le) (sq_nonneg _))

#print axioms four_law_cartesian_order
#print axioms cartesian_det
#print axioms four_law_regular_order
end Direction2.Feeding
