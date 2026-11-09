import BanachIsometric.EquatorCoordinates

/-! The actual closed hemisphere is a cone over its actual equator. The cone
parameterization is a continuous compact quotient map; only the pole fiber
is collapsed. This will descend actual equatorial null-homotopies. -/

noncomputable section

namespace BanachIsometric

open Set Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem unitInterval_one_sub_sq_nonneg (t : unitInterval) : 0 ≤ 1 - (t : ℝ) ^ 2 := by
  nlinarith [t.property.1, t.property.2]

theorem hemisphereCone_norm (v : sphere (0 : V) 1) (t : unitInterval) (z : EquatorSphere v) :
    ‖Real.sqrt (1 - (t : ℝ) ^ 2) • v.val + (t : ℝ) • z.val.val‖ = 1 := by
  have hvv : inner ℝ v.val v.val = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v]; norm_num
  have hzz : inner ℝ z.val.val z.val.val = 1 := by
    rw [real_inner_self_eq_norm_sq, show ‖z.val.val‖ = 1 from norm_eq_of_mem_sphere z]; norm_num
  have hvz : inner ℝ v.val z.val.val = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.val.property
  have hzv : inner ℝ z.val.val v.val = 0 := by rw [real_inner_comm, hvz]
  have hs := Real.sq_sqrt (unitInterval_one_sub_sq_nonneg t)
  have hn : ‖Real.sqrt (1 - (t : ℝ) ^ 2) • v.val + (t : ℝ) • z.val.val‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hvv, hzz, hvz, hzv, mul_one, mul_zero, zero_add, add_zero]
    nlinarith
  nlinarith [norm_nonneg (Real.sqrt (1 - (t : ℝ) ^ 2) • v.val + (t : ℝ) • z.val.val)]

def hemisphereCone (v : sphere (0 : V) 1) :
    C(unitInterval × EquatorSphere v, closedHemisphere v) := by
  refine ⟨fun x => ⟨⟨Real.sqrt (1 - (x.1 : ℝ) ^ 2) • v.val + (x.1 : ℝ) • x.2.val.val, ?_⟩, ?_⟩, ?_⟩
  · rw [Metric.mem_sphere, dist_zero_right]
    exact hemisphereCone_norm v x.1 x.2
  · change 0 ≤ inner ℝ v.val
      (Real.sqrt (1 - (x.1 : ℝ) ^ 2) • v.val + (x.1 : ℝ) • x.2.val.val)
    have hvv : inner ℝ v.val v.val = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v]; norm_num
    have hvz : inner ℝ v.val x.2.val.val = 0 := equatorInclusion_inner v x.2
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hvv, hvz,
      mul_one, mul_zero, add_zero]
    exact Real.sqrt_nonneg _
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact ((continuous_const.sub ((continuous_subtype_val.comp continuous_fst).pow 2)).sqrt.smul
      continuous_const).add ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))

@[simp] theorem hemisphereCone_val (v : sphere (0 : V) 1) (t : unitInterval) (z : EquatorSphere v) :
    (hemisphereCone v (t, z)).val.val =
      Real.sqrt (1 - (t : ℝ) ^ 2) • v.val + (t : ℝ) • z.val.val := rfl

theorem hemisphereCone_inner (v : sphere (0 : V) 1) (t : unitInterval) (z : EquatorSphere v) :
    inner ℝ v.val (hemisphereCone v (t, z)).val.val = Real.sqrt (1 - (t : ℝ) ^ 2) := by
  have hvz : inner ℝ v.val z.val.val = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.val.property
  rw [hemisphereCone_val, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    hvz, mul_zero, add_zero, real_inner_self_eq_norm_sq,
    norm_eq_of_mem_sphere v]
  simp

theorem hemisphereCone_fiber (v : sphere (0 : V) 1) (t u : unitInterval) (z w : EquatorSphere v)
    (h : hemisphereCone v (t, z) = hemisphereCone v (u, w)) :
    t = u ∧ (t = 0 ∨ z = w) := by
  have hi := congrArg (fun x : closedHemisphere v => inner ℝ v.val x.val.val) h
  change inner ℝ v.val (hemisphereCone v (t, z)).val.val =
    inner ℝ v.val (hemisphereCone v (u, w)).val.val at hi
  rw [hemisphereCone_inner, hemisphereCone_inner] at hi
  have hsq := congrArg (fun a : ℝ => a ^ 2) hi
  change Real.sqrt (1 - (t : ℝ) ^ 2) ^ 2 = Real.sqrt (1 - (u : ℝ) ^ 2) ^ 2 at hsq
  rw [Real.sq_sqrt (unitInterval_one_sub_sq_nonneg t),
    Real.sq_sqrt (unitInterval_one_sub_sq_nonneg u)] at hsq
  have htu : t = u := Subtype.ext (by nlinarith [t.property.1, u.property.1])
  subst u
  refine ⟨rfl, ?_⟩
  by_cases ht : t = 0
  · exact Or.inl ht
  · right
    have ht0 : (t : ℝ) ≠ 0 := fun he => ht (Subtype.ext he)
    have hv := congrArg (fun x : closedHemisphere v => x.val.val) h
    change Real.sqrt (1 - (t : ℝ) ^ 2) • v.val + (t : ℝ) • z.val.val =
      Real.sqrt (1 - (t : ℝ) ^ 2) • v.val + (t : ℝ) • w.val.val at hv
    have hz := congrArg (fun x : V => (t : ℝ)⁻¹ • x) (add_left_cancel hv)
    simp only [smul_smul, inv_mul_cancel₀ ht0, one_smul] at hz
    exact Subtype.ext (Subtype.ext hz)

end BanachIsometric
