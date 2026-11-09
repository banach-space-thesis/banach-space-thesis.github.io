import BanachIsometric.QuaternionicHyperplaneField

/-! Operator regularity of the actual quaternionic projection. Its four
real rank-one terms give a genuine global Lipschitz estimate in the original
Euclidean operator norm. A finite constant 8 suffices for the paper. -/

namespace BanachIsometric.Quaternionic

open scoped Quaternion NNReal

noncomputable section

theorem norm_i : ‖i‖ = 1 := by
  have h := normSq_i
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  nlinarith [norm_nonneg i]

theorem norm_j : ‖j‖ = 1 := by
  have h := normSq_j
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  nlinarith [norm_nonneg j]

theorem norm_k : ‖k‖ = 1 := by
  have h := normSq_k
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  nlinarith [norm_nonneg k]

def rightUnitIsometry (m : ℕ) (a : H) (ha : ‖a‖ = 1) : Euclidean m →ₗᵢ[ℝ] Euclidean m where
  toLinearMap :=
    { toFun := fun x => rightMul x a
      map_add' := fun x y => rightMul_add_left x y a
      map_smul' := fun r x => by
        apply PiLp.ext
        intro q
        change (r • x q) * a = r • (x q * a)
        exact smul_mul_assoc r (x q) a }
  norm_map' x := by
    change ‖rightMul x a‖ = ‖x‖
    rw [norm_rightMul, ha, mul_one]

def realRankOne {m : ℕ} (u : Euclidean m) : Euclidean m →L[ℝ] Euclidean m :=
  (innerSL ℝ u).smulRight u

theorem norm_realRankOne_sub_le {m : ℕ} (u v : Euclidean m) :
    ‖realRankOne u - realRankOne v‖ ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have hdec : realRankOne u - realRankOne v =
      (innerSL ℝ u).smulRight (u - v) + (innerSL ℝ u - innerSL ℝ v).smulRight v := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [realRankOne, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, smul_sub, sub_smul]
    abel
  rw [hdec]
  calc
    _ ≤ ‖(innerSL ℝ u).smulRight (u - v)‖ + ‖(innerSL ℝ u - innerSL ℝ v).smulRight v‖ := norm_add_le _ _
    _ = (‖u‖ + ‖v‖) * ‖u - v‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply,
        innerSL_apply_norm, ← (innerSL ℝ).map_sub u v, innerSL_apply_norm]
      ring

theorem standardHermitian_imI (m : ℕ) (u v : Euclidean m) :
    ((standardHermitian m).form u v).imI = inner ℝ (rightMul u i) v := by
  have h := standardHermitian_re m (rightMul u i) v
  rw [(standardHermitian m).mul_left] at h
  simpa [Quaternion.re_mul, i] using h

theorem standardHermitian_imJ (m : ℕ) (u v : Euclidean m) :
    ((standardHermitian m).form u v).imJ = inner ℝ (rightMul u j) v := by
  have h := standardHermitian_re m (rightMul u j) v
  rw [(standardHermitian m).mul_left] at h
  simpa [Quaternion.re_mul, j] using h

theorem standardHermitian_imK (m : ℕ) (u v : Euclidean m) :
    ((standardHermitian m).form u v).imK = inner ℝ (rightMul u k) v := by
  have h := standardHermitian_re m (rightMul u k) v
  rw [(standardHermitian m).mul_left] at h
  simpa [Quaternion.re_mul, k] using h

theorem normalProjection_eq_four_rankOne (m : ℕ) (u : Euclidean m) :
    normalProjection m u = 1 -
      (realRankOne u + realRankOne (rightMul u i) + realRankOne (rightMul u j) + realRankOne (rightMul u k)) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [normalProjection_apply, rightMul_decompose, standardHermitian_re,
    standardHermitian_imI, standardHermitian_imJ, standardHermitian_imK]
  rfl

theorem realRankOne_right_unit_lipschitz (m : ℕ) (a : H) (ha : ‖a‖ = 1) :
    LipschitzWith 2 (fun u : Metric.sphere (0 : Euclidean m) 1 => realRankOne (rightMul u.val a)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hu : ‖u.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hv : ‖v.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  have h := norm_realRankOne_sub_le (rightMul u.val a) (rightMul v.val a)
  have hsub : rightMul u.val a - rightMul v.val a = rightMul (u.val - v.val) a := by
    simp only [rightMul, smul_sub]
  simpa only [norm_rightMul, hu, hv, ha, mul_one, one_add_one_eq_two,
    ← dist_eq_norm, Subtype.dist_eq, NNReal.coe_ofNat, hsub] using h

theorem normalProjection_lipschitz (m : ℕ) :
    LipschitzWith 8 (fun u : Metric.sphere (0 : Euclidean m) 1 => normalProjection m u.val) := by
  have h1 := realRankOne_right_unit_lipschitz m 1 norm_one
  have hi := realRankOne_right_unit_lipschitz m i norm_i
  have hj := realRankOne_right_unit_lipschitz m j norm_j
  have hk := realRankOne_right_unit_lipschitz m k norm_k
  have hsum := ((h1.add hi).add hj).add hk
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [normalProjection_eq_four_rankOne, normalProjection_eq_four_rankOne]
  have hd := hsum.dist_le_mul u v
  simp only [rightMul_one] at hd
  calc
    _ = dist (realRankOne u.val + realRankOne (rightMul u.val i) + realRankOne (rightMul u.val j) + realRankOne (rightMul u.val k))
      (realRankOne v.val + realRankOne (rightMul v.val i) + realRankOne (rightMul v.val j) + realRankOne (rightMul v.val k)) := by
      let A : Euclidean m →L[ℝ] Euclidean m := realRankOne u.val + realRankOne (rightMul u.val i) +
        realRankOne (rightMul u.val j) + realRankOne (rightMul u.val k)
      let B : Euclidean m →L[ℝ] Euclidean m := realRankOne v.val + realRankOne (rightMul v.val i) +
        realRankOne (rightMul v.val j) + realRankOne (rightMul v.val k)
      change dist (1 - A) (1 - B) = dist A B
      calc
        _ = ‖(1 - A) - (1 - B)‖ := dist_eq_norm (1 - A) (1 - B)
        _ = ‖A - B‖ := by
          rw [show (1 - A) - (1 - B) = -(A - B) by abel]
          exact norm_neg (A - B)
        _ = dist A B := (dist_eq_norm A B).symm
    _ ≤ (8 : ℝ) * dist u v := by norm_num at hd ⊢; exact hd

theorem realNormalHyperplane_projection_lipschitz (m : ℕ) :
    LipschitzWith 8 (fun u : Metric.sphere (0 : Euclidean m) 1 => (realNormalHyperplane m u.val).starProjection) := by
  have heq : (fun u : Metric.sphere (0 : Euclidean m) 1 => (realNormalHyperplane m u.val).starProjection) =
      fun u => normalProjection m u.val := by
    funext u
    exact (normalProjection_eq_starProjection m u.val
      (by simpa only [Metric.mem_sphere, dist_zero_right] using u.property)).symm
  rw [heq]
  exact normalProjection_lipschitz m

end
end BanachIsometric.Quaternionic
