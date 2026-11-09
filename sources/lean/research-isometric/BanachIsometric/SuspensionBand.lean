import BanachIsometric.SuspensionHeightFibers

/-! The literal signed-height equatorial band and the exact action of the
actual conewise suspension on it. The identity is a statement about actual
vectors and maps; a degree or orientation comparison is not assumed. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def equatorBandVector (v : sphere (0 : V) 1) (a : ℝ) (z : EquatorSphere v) : V :=
  a • v.val + Real.sqrt (1 - a ^ 2) • z.val.val

theorem equatorBandVector_norm (v : sphere (0 : V) 1) (a : Icc (-1 : ℝ) 1)
    (z : EquatorSphere v) : ‖equatorBandVector v a z‖ = 1 := by
  have hrad : 0 ≤ 1 - (a : ℝ) ^ 2 := by nlinarith [a.property.1, a.property.2]
  have hvv : inner ℝ v.val v.val = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v]; norm_num
  have hzz : inner ℝ z.val.val z.val.val = 1 := by
    rw [real_inner_self_eq_norm_sq, show ‖z.val.val‖ = 1 from norm_eq_of_mem_sphere z]; norm_num
  have hvz : inner ℝ v.val z.val.val = 0 := equatorInclusion_inner v z
  have hzv : inner ℝ z.val.val v.val = 0 := by rw [real_inner_comm, hvz]
  have hsq : ‖equatorBandVector v a z‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [equatorBandVector, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hvv, hzz, hvz, hzv, mul_one, mul_zero, zero_add, add_zero]
    nlinarith [Real.sq_sqrt hrad]
  nlinarith [norm_nonneg (equatorBandVector v a z)]

def equatorBand (v : sphere (0 : V) 1) :
    C(Icc (-1 : ℝ) 1 × EquatorSphere v, sphere (0 : V) 1) := by
  refine ⟨fun p => ⟨equatorBandVector v p.1 p.2, ?_⟩, ?_⟩
  · rw [mem_sphere, dist_zero_right]
    exact equatorBandVector_norm v p.1 p.2
  · apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
      (((continuous_const.sub ((continuous_subtype_val.comp continuous_fst).pow 2)).sqrt).smul
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))

theorem equatorBand_inner (v : sphere (0 : V) 1) (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v) :
    inner ℝ v.val (equatorBand v (a, z)).val = a := by
  have hz : inner ℝ v.val z.val.val = 0 := equatorInclusion_inner v z
  change inner ℝ v.val ((a : ℝ) • v.val + Real.sqrt (1 - (a : ℝ) ^ 2) • z.val.val) = a
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    hz, mul_zero, add_zero, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v]
  norm_num

theorem suspension_equatorBand [FiniteDimensional ℝ V]
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hN : ∀ x : closedHemisphere v, φ x.val = (hemisphereMap v q₀ f x).val)
    (hS : ∀ x : closedHemisphere (-v), φ x.val =
      (hemisphereMap (-v) (equatorOppositePole v q₀) (oppositeEquatorMap v f) x).val)
    (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v) :
    φ (equatorBand v (a, z)) = equatorBand v (a, f z) := by
  have hrad : 0 ≤ 1 - (a : ℝ) ^ 2 := by nlinarith [a.property.1, a.property.2]
  have hle : Real.sqrt (1 - (a : ℝ) ^ 2) ≤ 1 := by
    have h := Real.sq_sqrt hrad
    nlinarith [Real.sqrt_nonneg (1 - (a : ℝ) ^ 2), sq_nonneg (a : ℝ)]
  let t : unitInterval := ⟨Real.sqrt (1 - (a : ℝ) ^ 2), Real.sqrt_nonneg _, hle⟩
  by_cases ha : 0 ≤ (a : ℝ)
  · have he (w : EquatorSphere v) : equatorBand v (a, w) = (hemisphereCone v (t, w)).val := by
      apply Subtype.ext
      change (a : ℝ) • v.val + Real.sqrt (1 - (a : ℝ) ^ 2) • w.val.val =
        Real.sqrt (1 - Real.sqrt (1 - (a : ℝ) ^ 2) ^ 2) • v.val +
          Real.sqrt (1 - (a : ℝ) ^ 2) • w.val.val
      rw [Real.sq_sqrt hrad, show 1 - (1 - (a : ℝ) ^ 2) = (a : ℝ) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
    rw [he z, hN, hemisphereMap_cone, ← he (f z)]
  · have ha' : (a : ℝ) ≤ 0 := (lt_of_not_ge ha).le
    have he (w : EquatorSphere v) : equatorBand v (a, w) =
        (hemisphereCone (-v) (t, equatorOppositePole v w)).val := by
      apply Subtype.ext
      change (a : ℝ) • v.val + Real.sqrt (1 - (a : ℝ) ^ 2) • w.val.val =
        Real.sqrt (1 - Real.sqrt (1 - (a : ℝ) ^ 2) ^ 2) • (-v.val) +
          Real.sqrt (1 - (a : ℝ) ^ 2) • w.val.val
      rw [Real.sq_sqrt hrad, show 1 - (1 - (a : ℝ) ^ 2) = (a : ℝ) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonpos ha']
      simp only [smul_neg, neg_smul, neg_neg]
    have hef : oppositeEquatorMap v f (equatorOppositePole v z) = equatorOppositePole v (f z) := by
      change equatorOppositePole v (f ((equatorOppositePole v).symm (equatorOppositePole v z))) = _
      rw [Homeomorph.symm_apply_apply]
    rw [he z, hS, hemisphereMap_cone, hef, ← he (f z)]

end BanachIsometric
