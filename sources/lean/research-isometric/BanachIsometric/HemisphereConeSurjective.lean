import BanachIsometric.HemisphereCone

/-! Surjectivity and the compact quotient property of the actual hemisphere
cone parameterization. -/

noncomputable section

namespace BanachIsometric

open Set Metric Topology
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def hemisphereTangentialPart (v : sphere (0 : V) 1) (x : closedHemisphere v) : (ℝ ∙ v.val)ᗮ := by
  refine ⟨x.val.val - (inner ℝ v.val x.val.val) • v.val, ?_⟩
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_eq_of_mem_sphere v]
  simp

theorem hemisphereTangentialPart_decomposition (v : sphere (0 : V) 1) (x : closedHemisphere v) :
    (inner ℝ v.val x.val.val) • v.val + (hemisphereTangentialPart v x).val = x.val.val := by
  change (inner ℝ v.val x.val.val) • v.val +
    (x.val.val - (inner ℝ v.val x.val.val) • v.val) = x.val.val
  abel

theorem hemisphere_height_norm_identity (v : sphere (0 : V) 1) (x : closedHemisphere v) :
    (inner ℝ v.val x.val.val) ^ 2 + ‖hemisphereTangentialPart v x‖ ^ 2 = 1 := by
  have hvv : inner ℝ v.val v.val = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v]; norm_num
  have hxx : inner ℝ x.val.val x.val.val = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x.val]; norm_num
  have hxv : inner ℝ x.val.val v.val = inner ℝ v.val x.val.val := real_inner_comm _ _
  change (inner ℝ v.val x.val.val) ^ 2 +
    ‖x.val.val - (inner ℝ v.val x.val.val) • v.val‖ ^ 2 = 1
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hxx, hvv, hxv]
  ring

theorem hemisphereCone_surjective (v : sphere (0 : V) 1) (q₀ : EquatorSphere v) :
    Function.Surjective (hemisphereCone v) := by
  intro x
  let a := inner ℝ v.val x.val.val
  let u := hemisphereTangentialPart v x
  let r := ‖u‖
  have ha : 0 ≤ a := x.property
  have hr : 0 ≤ r := norm_nonneg u
  have he : a ^ 2 + r ^ 2 = 1 := hemisphere_height_norm_identity v x
  have hr1 : r ≤ 1 := by nlinarith [sq_nonneg a]
  have hsqrt : Real.sqrt (1 - r ^ 2) = a := by
    rw [show 1 - r ^ 2 = a ^ 2 by linarith, Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  by_cases hr0 : r = 0
  · have hu0 : u = 0 := norm_eq_zero.mp hr0
    have ha1 : a = 1 := by rw [hr0] at he; nlinarith
    refine ⟨(0, q₀), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hd := hemisphereTangentialPart_decomposition v x
    change a • v.val + u.val = x.val.val at hd
    rw [hu0, Submodule.coe_zero, ha1, one_smul, add_zero] at hd
    change Real.sqrt (1 - (0 : ℝ) ^ 2) • v.val + (0 : ℝ) • q₀.val.val = x.val.val
    simpa using hd
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let z : EquatorSphere v := ⟨r⁻¹ • u, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hrpos)]
      exact inv_mul_cancel₀ hr0⟩
    let t : unitInterval := ⟨r, hr, hr1⟩
    refine ⟨(t, z), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change Real.sqrt (1 - r ^ 2) • v.val + r • (r⁻¹ • u.val) = x.val.val
    rw [hsqrt, smul_smul, mul_inv_cancel₀ hr0, one_smul]
    exact hemisphereTangentialPart_decomposition v x

theorem isQuotientMap_hemisphereCone [FiniteDimensional ℝ V]
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v) : IsQuotientMap (hemisphereCone v) := by
  letI : CompactSpace (EquatorSphere v) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (ℝ ∙ v.val)ᗮ) 1)
  exact (hemisphereCone v).continuous.isClosedMap.isQuotientMap
    (hemisphereCone v).continuous (hemisphereCone_surjective v q₀)

end BanachIsometric
