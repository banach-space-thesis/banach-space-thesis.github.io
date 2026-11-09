import LindenstraussRetraction.SummationApproximation
import LindenstraussRetraction.Renorming

/-! Explicit finite blocks of the summation space and its anisotropic renormings. -/

noncomputable section
open Filter Topology
open scoped BigOperators ENNReal

namespace LindenstraussRetraction

universe v
variable (𝕜 : Type v) [RCLike 𝕜]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option synthInstance.maxSize 512

local instance blocksSummationNormedGroup : NormedAddCommGroup (SummationSpace 𝕜) := inferInstance
local instance blocksSummationNormedSpace : NormedSpace 𝕜 (SummationSpace 𝕜) := inferInstance

/-- Evaluation at one block of the dependent ℓ₁ sum. -/
def summationBlockEvaluation (m : ℕ) :
    SummationSpace 𝕜 →L[𝕜] FiniteCoordinateSpace 𝕜 m :=
  ({ toFun := fun u => u m
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : _ →ₗ[𝕜] _).mkContinuous 1 (by
    intro u
    simpa only [one_mul] using lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0) u m)

@[simp] theorem summationBlockEvaluation_apply (m : ℕ) (u : SummationSpace 𝕜) :
    summationBlockEvaluation 𝕜 m u = u m := rfl

/-- The copy of `E_(m+1)` in the difference `A_(m+1)-A_m`. -/
def summationBlockEmbedding (m : ℕ) :
    FiniteCoordinateSpace 𝕜 m →L[𝕜] SummationSpace 𝕜 :=
  (ContinuousLinearMap.id 𝕜 _ - summationApproximationOperator 𝕜 m).comp
    (lp.singleContinuousLinearMap 𝕜 (FiniteCoordinateSpace 𝕜) 1 m)

@[simp] theorem summationBlockEmbedding_apply (m : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    summationBlockEmbedding 𝕜 m x = lp.single 1 m x -
      summationApproximationOperator 𝕜 m (lp.single 1 m x) := rfl

/-- The top block of `A_(m+1)u`, viewed as a finite-coordinate vector. -/
def summationBlockCoordinate (m : ℕ) :
    SummationSpace 𝕜 →L[𝕜] FiniteCoordinateSpace 𝕜 m :=
  (summationBlockEvaluation 𝕜 m).comp (summationApproximationOperator 𝕜 (m+1))

@[simp] theorem summationBlockCoordinate_apply (m : ℕ) (u : SummationSpace 𝕜) :
    summationBlockCoordinate 𝕜 m u = summationApproximationOperator 𝕜 (m+1) u m := rfl

theorem summationApproximation_single_fix (m N : ℕ) (h : m < N)
    (x : FiniteCoordinateSpace 𝕜 m) :
    summationApproximationOperator 𝕜 N (lp.single 1 m x) = lp.single 1 m x := by
  apply summationApproximationOperator_fix
  intro k hk
  exact lp.single_apply_ne _ _ _ (ne_of_gt (h.trans_le hk))

theorem summationApproximation_blockEmbedding (N m : ℕ)
    (x : FiniteCoordinateSpace 𝕜 m) :
    summationApproximationOperator 𝕜 N (summationBlockEmbedding 𝕜 m x) =
      if m < N then summationBlockEmbedding 𝕜 m x else 0 := by
  rw [summationBlockEmbedding_apply, map_sub]
  have hc := congrArg (fun T : SummationSpace 𝕜 →L[𝕜] SummationSpace 𝕜 =>
    T (lp.single 1 m x)) (summationApproximationOperator_comp 𝕜 N m)
  change summationApproximationOperator 𝕜 N
    (summationApproximationOperator 𝕜 m (lp.single 1 m x)) = _ at hc
  by_cases h : m < N
  · rw [if_pos h, summationApproximation_single_fix 𝕜 m N h, hc, min_eq_right h.le]
  · rw [if_neg h, hc, min_eq_left (Nat.le_of_not_gt h), sub_self]

theorem summationBlockEmbedding_top (m : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    summationBlockEmbedding 𝕜 m x m = x := by
  rw [summationBlockEmbedding_apply]
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.single_apply_self,
    summationApproximationOperator_apply_eq_zero 𝕜 m m le_rfl, sub_zero]

theorem summationBlockEmbedding_difference (m : ℕ) (u : SummationSpace 𝕜) :
    summationBlockEmbedding 𝕜 m (summationBlockCoordinate 𝕜 m u) =
      summationApproximationOperator 𝕜 (m+1) u - summationApproximationOperator 𝕜 m u := by
  let a := summationApproximationOperator 𝕜 (m+1) u
  have htail : a - summationHead 𝕜 m a = lp.single 1 m (a m) := by
    apply lp.ext
    funext k
    by_cases hkm : k = m
    · subst k; simp
    · by_cases hk : k < m
      · simp [summationHead_apply, hk, hkm]
      · have haz : a k = 0 := summationApproximationOperator_apply_eq_zero 𝕜 (m+1) k
          (by omega) u
        simp [summationHead_apply, hk, hkm, haz]
  have hhead : summationApproximationOperator 𝕜 m (summationHead 𝕜 m a) =
      summationHead 𝕜 m a := by
    apply summationApproximationOperator_fix
    intro k hk
    simp [summationHead_apply, not_lt.mpr hk]
  have hc : summationApproximationOperator 𝕜 m a = summationApproximationOperator 𝕜 m u :=
    summationApproximationOperator_comp_small 𝕜 m (m+1) (Nat.le_succ m) u
  change lp.single 1 m (a m) - summationApproximationOperator 𝕜 m (lp.single 1 m (a m)) = _
  rw [← htail, map_sub, hhead, hc]
  change a - summationHead 𝕜 m a -
      (summationApproximationOperator 𝕜 m u - summationHead 𝕜 m a) = a - _
  abel

theorem summationBlockCoordinate_embedding (m n : ℕ)
    (x : FiniteCoordinateSpace 𝕜 n) :
    summationBlockCoordinate 𝕜 m (summationBlockEmbedding 𝕜 n x) =
      if h : m = n then h.symm ▸ x else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [dif_pos rfl, summationBlockCoordinate_apply,
      summationApproximation_blockEmbedding, if_pos (Nat.lt_succ_self m),
      summationBlockEmbedding_top]
  · rw [dif_neg hmn, summationBlockCoordinate_apply, summationApproximation_blockEmbedding]
    by_cases h : n < m+1
    · rw [if_pos h, summationBlockEmbedding_apply]
      have hnm : n < m := by omega
      simp only [lp.coeFn_sub, Pi.sub_apply,
        lp.single_apply_ne _ _ _ hmn,
        summationApproximationOperator_apply_eq_zero 𝕜 n m hnm.le, sub_zero]
    · rw [if_neg h]
      rfl

/-- Projection onto the first `r` scalar coordinates inside a finite block. -/
def finiteCoordinateTruncation (m r : ℕ) :
    FiniteCoordinateSpace 𝕜 m →L[𝕜] FiniteCoordinateSpace 𝕜 m :=
  ((c0TruncationOperator 𝕜 r).comp (finiteCoordinateSubmodule 𝕜 m).subtypeL).codRestrict
    (finiteCoordinateSubmodule 𝕜 m) (by
      intro x k hk
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        c0TruncationOperator_apply, c0Truncation_apply]
      split_ifs
      · exact x.property k hk
      · rfl)

@[simp] theorem finiteCoordinateTruncation_coe (m r : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    (finiteCoordinateTruncation 𝕜 m r x).val = c0Truncation 𝕜 r x.val := rfl

theorem norm_finiteCoordinateTruncation_le (m r : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    ‖finiteCoordinateTruncation 𝕜 m r x‖ ≤ ‖x‖ := norm_c0Truncation_le 𝕜 r x.val

theorem summationHead_single_zero (M n : ℕ) (h : M ≤ n)
    (x : FiniteCoordinateSpace 𝕜 n) : summationHead 𝕜 M (lp.single 1 n x) = 0 := by
  apply lp.ext
  funext k
  rw [summationHead_apply]
  split_ifs with hk
  · exact lp.single_apply_ne _ _ _ (ne_of_lt (hk.trans_le h))
  · rfl

@[simp] theorem summationBlockEmbedding_zero (x : FiniteCoordinateSpace 𝕜 0) :
    summationBlockEmbedding 𝕜 0 x = lp.single 1 0 x := by
  simp [summationBlockEmbedding_apply]

theorem summationBlockEmbedding_succ (m : ℕ) (x : FiniteCoordinateSpace 𝕜 (m+1)) :
    summationBlockEmbedding 𝕜 (m+1) x = lp.single 1 (m+1) x -
      summationApproximateLift 𝕜 m x.val := by
  rw [summationBlockEmbedding_apply, summationApproximationOperator_succ_apply,
    summationHead_single_zero 𝕜 m (m+1) (Nat.le_succ m), sub_zero,
    summationOperator_single, zero_add]

theorem norm_single_sub_single (n m : ℕ) (h : n ≠ m)
    (x : FiniteCoordinateSpace 𝕜 n) (y : FiniteCoordinateSpace 𝕜 m) :
    ‖lp.single 1 n x - lp.single 1 m y‖ = ‖x‖ + ‖y‖ := by
  let u : SummationSpace 𝕜 := lp.single 1 n x - lp.single 1 m y
  have hun : u n = x := by simp [u, Ne.symm h]
  have hres : u - lp.single 1 n (u n) = -lp.single 1 m y := by rw [hun]; dsimp [u]; abel
  have hn := lp.norm_compl_sum_single (p := (1 : ℝ≥0∞)) (by norm_num) u {n}
  simp only [Finset.sum_singleton, Real.rpow_one, ENNReal.toReal_one] at hn
  rw [hres, norm_neg, lp.norm_single (by norm_num), hun] at hn
  change ‖u‖ = ‖x‖ + ‖y‖
  linarith

theorem norm_summationBlockEmbedding (m : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    ‖summationBlockEmbedding 𝕜 m x‖ = ‖x‖ + ‖c0Truncation 𝕜 m x.val‖ := by
  cases m with
  | zero =>
    rw [summationBlockEmbedding_zero, lp.norm_single (by norm_num)]
    have hz : c0Truncation 𝕜 0 x.val = 0 := by ext k; simp
    simp [hz]
  | succ m =>
    rw [summationBlockEmbedding_succ, summationApproximateLift_apply,
      norm_single_sub_single 𝕜 (m+1) m (Nat.succ_ne_self m)]
    rfl

theorem summationOperator_blockEmbedding (m : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    summationOperator 𝕜 (summationBlockEmbedding 𝕜 m x) = x.val - c0Truncation 𝕜 m x.val := by
  rw [summationBlockEmbedding_apply, map_sub, summationOperator_approximation,
    summationOperator_single]

theorem norm_summationBlockEmbedding_truncation_le (m r : ℕ)
    (x : FiniteCoordinateSpace 𝕜 m) :
    ‖summationBlockEmbedding 𝕜 m (finiteCoordinateTruncation 𝕜 m r x)‖ ≤
      ‖summationBlockEmbedding 𝕜 m x‖ := by
  rw [norm_summationBlockEmbedding, norm_summationBlockEmbedding]
  apply add_le_add (norm_finiteCoordinateTruncation_le 𝕜 m r x)
  rw [finiteCoordinateTruncation_coe, c0Truncation_comp]
  have heq : c0Truncation 𝕜 (min m r) x.val =
      c0Truncation 𝕜 r (c0Truncation 𝕜 m x.val) := by rw [c0Truncation_comp, min_comm]
  rw [heq]
  exact norm_c0Truncation_le 𝕜 r _

theorem norm_summationOperator_blockTruncation_le (m r : ℕ)
    (x : FiniteCoordinateSpace 𝕜 m) :
    ‖summationOperator 𝕜 (summationBlockEmbedding 𝕜 m (finiteCoordinateTruncation 𝕜 m r x))‖ ≤
      ‖summationOperator 𝕜 (summationBlockEmbedding 𝕜 m x)‖ := by
  by_cases h : r ≤ m
  · rw [summationOperator_blockEmbedding, finiteCoordinateTruncation_coe,
      c0Truncation_comp, min_eq_right h, sub_self, norm_zero]
    exact norm_nonneg _
  · have hmr : m+1 ≤ r := by omega
    have hfix : finiteCoordinateTruncation 𝕜 m r x = x := by
      apply Subtype.ext
      exact c0Truncation_fix_of_le 𝕜 hmr x
    rw [hfix]

/-- The usual scalar coordinate vector in `E_(m+1)`. -/
def finiteCoordinateUnit (m : ℕ) (j : Fin (m+1)) : FiniteCoordinateSpace 𝕜 m :=
  ⟨{ toFun := fun k => if k = j.val then 1 else 0
     continuous_toFun := continuous_of_discreteTopology
     zero_at_infty' := by
       rw [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
       apply tendsto_const_nhds.congr'
       filter_upwards [eventually_gt_atTop j.val] with k hk
       simp [ne_of_gt hk] }, by
     intro k hk
     simp [ne_of_gt (j.isLt.trans_le hk)]⟩

@[simp] theorem finiteCoordinateUnit_apply (m : ℕ) (j : Fin (m+1)) (k : ℕ) :
    (finiteCoordinateUnit 𝕜 m j).val k = if k = j.val then 1 else 0 := rfl

/-- A scalar coordinate, as a continuous functional on the finite block. -/
def finiteCoordinateEvaluation (m : ℕ) (j : Fin (m+1)) :
    FiniteCoordinateSpace 𝕜 m →L[𝕜] 𝕜 :=
  ({ toFun := fun x => x.val j.val
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : _ →ₗ[𝕜] _).mkContinuous 1 (by
       intro x
       simpa only [one_mul] using x.val.toBCF.norm_coe_le_norm j.val)

@[simp] theorem finiteCoordinateEvaluation_apply (m : ℕ) (j : Fin (m+1))
    (x : FiniteCoordinateSpace 𝕜 m) : finiteCoordinateEvaluation 𝕜 m j x = x.val j.val := rfl

theorem finiteCoordinateEvaluation_unit (m : ℕ) (j k : Fin (m+1)) :
    finiteCoordinateEvaluation 𝕜 m j (finiteCoordinateUnit 𝕜 m k) =
      if j = k then 1 else 0 := by
  simp only [finiteCoordinateEvaluation_apply, finiteCoordinateUnit_apply, Fin.ext_iff]

theorem finiteCoordinateTruncation_zero (m : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    finiteCoordinateTruncation 𝕜 m 0 x = 0 := by
  apply Subtype.ext
  ext k
  simp

theorem finiteCoordinateTruncation_full (m : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    finiteCoordinateTruncation 𝕜 m (m+1) x = x := by
  apply Subtype.ext
  exact c0Truncation_fix 𝕜 m x

theorem finiteCoordinateTruncation_step (m : ℕ) (j : Fin (m+1))
    (x : FiniteCoordinateSpace 𝕜 m) :
    finiteCoordinateTruncation 𝕜 m (j.val+1) x = finiteCoordinateTruncation 𝕜 m j.val x +
      finiteCoordinateEvaluation 𝕜 m j x • finiteCoordinateUnit 𝕜 m j := by
  apply Subtype.ext
  ext k
  change (if k < j.val+1 then x.val k else 0) =
    (if k < j.val then x.val k else 0) + x.val j.val • (if k = j.val then 1 else 0)
  by_cases hkj : k = j.val
  · subst k; simp
  · have heq : (k < j.val+1) ↔ k < j.val := by omega
    simp [hkj, heq]

theorem finiteCoordinate_sum_units (m : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    ∑ j : Fin (m+1), finiteCoordinateEvaluation 𝕜 m j x • finiteCoordinateUnit 𝕜 m j = x := by
  apply finiteCoordinateRestriction_injective 𝕜 m
  rw [map_sum]
  funext i
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply]
  change (∑ j : Fin (m+1), x.val j.val • (if i.val = j.val then 1 else 0)) = x.val i.val
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hij : i.val ≠ j.val := fun h => hj (Fin.ext h.symm)
    simp [hij]
  · simp

def summationScalarVector (m : ℕ) (j : Fin (m+1)) : SummationSpace 𝕜 :=
  summationBlockEmbedding 𝕜 m (finiteCoordinateUnit 𝕜 m j)

def summationScalarCoordinate (m : ℕ) (j : Fin (m+1)) : SummationSpace 𝕜 →L[𝕜] 𝕜 :=
  (finiteCoordinateEvaluation 𝕜 m j).comp (summationBlockCoordinate 𝕜 m)

theorem summationScalar_biorthogonal (m n : ℕ) (j : Fin (m+1)) (k : Fin (n+1)) :
    summationScalarCoordinate 𝕜 m j (summationScalarVector 𝕜 n k) =
      if (⟨m,j⟩ : Σ t : ℕ, Fin (t+1)) = ⟨n,k⟩ then 1 else 0 := by
  by_cases hmn : m = n
  · subst n
    change finiteCoordinateEvaluation 𝕜 m j
      (summationBlockCoordinate 𝕜 m (summationBlockEmbedding 𝕜 m (finiteCoordinateUnit 𝕜 m k))) = _
    rw [summationBlockCoordinate_embedding, dif_pos rfl, finiteCoordinateEvaluation_unit]
    simp
  · have hs : (⟨m,j⟩ : Σ t : ℕ, Fin (t+1)) ≠ ⟨n,k⟩ := by
      intro h
      exact hmn (congrArg Sigma.fst h)
    change finiteCoordinateEvaluation 𝕜 m j
      (summationBlockCoordinate 𝕜 m (summationBlockEmbedding 𝕜 n (finiteCoordinateUnit 𝕜 n k))) = _
    rw [summationBlockCoordinate_embedding, dif_neg hmn, map_zero, if_neg hs]

/-- The prefix after all blocks before `m` and the first `r` coordinates of block `m`. -/
def summationScalarProjection (m r : ℕ) : SummationSpace 𝕜 →L[𝕜] SummationSpace 𝕜 :=
  summationApproximationOperator 𝕜 m + (summationBlockEmbedding 𝕜 m).comp
    ((finiteCoordinateTruncation 𝕜 m r).comp (summationBlockCoordinate 𝕜 m))

@[simp] theorem summationScalarProjection_apply (m r : ℕ) (u : SummationSpace 𝕜) :
    summationScalarProjection 𝕜 m r u = summationApproximationOperator 𝕜 m u +
      summationBlockEmbedding 𝕜 m (finiteCoordinateTruncation 𝕜 m r (summationBlockCoordinate 𝕜 m u)) := rfl

theorem summationScalarProjection_zero (m : ℕ) :
    summationScalarProjection 𝕜 m 0 = summationApproximationOperator 𝕜 m := by
  apply ContinuousLinearMap.ext
  intro u
  simp [summationScalarProjection_apply, finiteCoordinateTruncation_zero]

theorem summationScalarProjection_boundary (m : ℕ) :
    summationScalarProjection 𝕜 m (m+1) = summationScalarProjection 𝕜 (m+1) 0 := by
  rw [summationScalarProjection_zero]
  apply ContinuousLinearMap.ext
  intro u
  rw [summationScalarProjection_apply, finiteCoordinateTruncation_full,
    summationBlockEmbedding_difference]
  abel

theorem summationScalarProjection_step (m : ℕ) (j : Fin (m+1)) :
    summationScalarProjection 𝕜 m (j.val+1) = summationScalarProjection 𝕜 m j.val +
      (summationScalarCoordinate 𝕜 m j).smulRight (summationScalarVector 𝕜 m j) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [summationScalarProjection_apply, finiteCoordinateTruncation_step,
    map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    summationScalarCoordinate, ContinuousLinearMap.comp_apply, summationScalarVector]
  abel

theorem summationScalar_fullBlock (m : ℕ) :
    (∑ j : Fin (m+1), (summationScalarCoordinate 𝕜 m j).smulRight (summationScalarVector 𝕜 m j)) =
      summationApproximationOperator 𝕜 (m+1) - summationApproximationOperator 𝕜 m := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.sub_apply, summationScalarCoordinate, summationScalarVector,
    ContinuousLinearMap.comp_apply]
  simp only [← map_smul]
  rw [← map_sum, finiteCoordinate_sum_units]
  exact summationBlockEmbedding_difference 𝕜 m u

theorem norm_toAnisotropic_summationApproximation_le {ε : ℝ} (hε : 0 ≤ ε)
    (N : ℕ) (u : SummationSpace 𝕜) :
    ‖toAnisotropic (summationOperator 𝕜) ε (summationApproximationOperator 𝕜 N u)‖ ≤
      ‖toAnisotropic (summationOperator 𝕜) ε u‖ := by
  rw [norm_toAnisotropic _ hε, norm_toAnisotropic _ hε, summationOperator_approximation]
  apply max_le_max
  · exact mul_le_mul_of_nonneg_left (summationApproximationOperator_norm_apply_le 𝕜 N u) hε
  · exact norm_c0Truncation_le 𝕜 N _

theorem norm_toAnisotropic_blockTruncation_le {ε : ℝ} (hε : 0 ≤ ε)
    (m r : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    ‖toAnisotropic (summationOperator 𝕜) ε
      (summationBlockEmbedding 𝕜 m (finiteCoordinateTruncation 𝕜 m r x))‖ ≤
      ‖toAnisotropic (summationOperator 𝕜) ε (summationBlockEmbedding 𝕜 m x)‖ := by
  rw [norm_toAnisotropic _ hε, norm_toAnisotropic _ hε]
  apply max_le_max
  · exact mul_le_mul_of_nonneg_left (norm_summationBlockEmbedding_truncation_le 𝕜 m r x) hε
  · exact norm_summationOperator_blockTruncation_le 𝕜 m r x

theorem norm_toAnisotropic_scalarProjection_le {ε : ℝ} (hε : 0 ≤ ε)
    (m r : ℕ) (u : SummationSpace 𝕜) :
    ‖toAnisotropic (summationOperator 𝕜) ε (summationScalarProjection 𝕜 m r u)‖ ≤
      3 * ‖toAnisotropic (summationOperator 𝕜) ε u‖ := by
  rw [summationScalarProjection_apply, map_add]
  calc
    _ ≤ ‖toAnisotropic (summationOperator 𝕜) ε (summationApproximationOperator 𝕜 m u)‖ +
        ‖toAnisotropic (summationOperator 𝕜) ε
          (summationBlockEmbedding 𝕜 m (finiteCoordinateTruncation 𝕜 m r
            (summationBlockCoordinate 𝕜 m u)))‖ := norm_add_le _ _
    _ ≤ ‖toAnisotropic (summationOperator 𝕜) ε u‖ +
        ‖toAnisotropic (summationOperator 𝕜) ε
          (summationBlockEmbedding 𝕜 m (summationBlockCoordinate 𝕜 m u))‖ :=
      add_le_add (norm_toAnisotropic_summationApproximation_le 𝕜 hε m u)
        (norm_toAnisotropic_blockTruncation_le 𝕜 hε m r _)
    _ ≤ ‖toAnisotropic (summationOperator 𝕜) ε u‖ +
        (‖toAnisotropic (summationOperator 𝕜) ε (summationApproximationOperator 𝕜 (m+1) u)‖ +
          ‖toAnisotropic (summationOperator 𝕜) ε (summationApproximationOperator 𝕜 m u)‖) := by
      rw [summationBlockEmbedding_difference, map_sub]
      exact add_le_add_left (norm_sub_le _ _) _
    _ ≤ ‖toAnisotropic (summationOperator 𝕜) ε u‖ +
        (‖toAnisotropic (summationOperator 𝕜) ε u‖ + ‖toAnisotropic (summationOperator 𝕜) ε u‖) :=
      add_le_add_left (add_le_add (norm_toAnisotropic_summationApproximation_le 𝕜 hε (m+1) u)
        (norm_toAnisotropic_summationApproximation_le 𝕜 hε m u)) _
    _ = _ := by ring

def anisotropicSummationScalarVector (ε : ℝ) (m : ℕ) (j : Fin (m+1)) :
    AnisotropicSpace (summationOperator 𝕜) ε :=
  toAnisotropic (summationOperator 𝕜) ε (summationScalarVector 𝕜 m j)

def anisotropicSummationScalarCoordinate (ε : ℝ) (m : ℕ) (j : Fin (m+1)) :
    AnisotropicSpace (summationOperator 𝕜) ε →L[𝕜] 𝕜 :=
  (summationScalarCoordinate 𝕜 m j).comp (fromAnisotropic (summationOperator 𝕜) ε)

def anisotropicSummationScalarProjection (ε : ℝ) (m r : ℕ) :
    AnisotropicSpace (summationOperator 𝕜) ε →L[𝕜] AnisotropicSpace (summationOperator 𝕜) ε :=
  (toAnisotropic (summationOperator 𝕜) ε).comp
    ((summationScalarProjection 𝕜 m r).comp (fromAnisotropic (summationOperator 𝕜) ε))

@[simp] theorem anisotropicSummationScalarProjection_apply (ε : ℝ) (m r : ℕ)
    (z : AnisotropicSpace (summationOperator 𝕜) ε) :
    anisotropicSummationScalarProjection 𝕜 ε m r z =
      toAnisotropic (summationOperator 𝕜) ε
        (summationScalarProjection 𝕜 m r (fromAnisotropic (summationOperator 𝕜) ε z)) := rfl

theorem anisotropicSummationScalar_biorthogonal {ε : ℝ} (hε : 0 < ε)
    (m n : ℕ) (j : Fin (m+1)) (k : Fin (n+1)) :
    anisotropicSummationScalarCoordinate 𝕜 ε m j (anisotropicSummationScalarVector 𝕜 ε n k) =
      if (⟨m,j⟩ : Σ t : ℕ, Fin (t+1)) = ⟨n,k⟩ then 1 else 0 := by
  change summationScalarCoordinate 𝕜 m j (fromAnisotropic (summationOperator 𝕜) ε
    (toAnisotropic (summationOperator 𝕜) ε (summationScalarVector 𝕜 n k))) = _
  rw [from_toAnisotropic _ hε]
  exact summationScalar_biorthogonal 𝕜 m n j k

theorem anisotropicSummationScalarProjection_zero (ε : ℝ) :
    anisotropicSummationScalarProjection 𝕜 ε 0 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  simp [anisotropicSummationScalarProjection_apply, summationScalarProjection_zero]

theorem anisotropicSummationScalarProjection_boundary (ε : ℝ) (m : ℕ) :
    anisotropicSummationScalarProjection 𝕜 ε m (m+1) =
      anisotropicSummationScalarProjection 𝕜 ε (m+1) 0 := by
  unfold anisotropicSummationScalarProjection
  rw [summationScalarProjection_boundary]

theorem anisotropicSummationScalarProjection_step (ε : ℝ) (m : ℕ) (j : Fin (m+1)) :
    anisotropicSummationScalarProjection 𝕜 ε m (j.val+1) =
      anisotropicSummationScalarProjection 𝕜 ε m j.val +
      (anisotropicSummationScalarCoordinate 𝕜 ε m j).smulRight
        (anisotropicSummationScalarVector 𝕜 ε m j) := by
  apply ContinuousLinearMap.ext
  intro z
  change toAnisotropic (summationOperator 𝕜) ε (summationScalarProjection 𝕜 m (j.val+1)
    (fromAnisotropic (summationOperator 𝕜) ε z)) = _
  rw [summationScalarProjection_step]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, map_add,
    map_smul, anisotropicSummationScalarProjection_apply, anisotropicSummationScalarCoordinate,
    anisotropicSummationScalarVector, ContinuousLinearMap.comp_apply]

theorem anisotropicSummationScalarProjection_norm_apply_le {ε : ℝ} (hε : 0 < ε)
    (m r : ℕ) (z : AnisotropicSpace (summationOperator 𝕜) ε) :
    ‖anisotropicSummationScalarProjection 𝕜 ε m r z‖ ≤ 3 * ‖z‖ := by
  have h := norm_toAnisotropic_scalarProjection_le 𝕜 hε.le m r
    (fromAnisotropic (summationOperator 𝕜) ε z)
  rw [to_fromAnisotropic _ hε] at h
  exact h

theorem norm_anisotropicSummationScalarProjection_le {ε : ℝ} (hε : 0 < ε) (m r : ℕ) :
    ‖anisotropicSummationScalarProjection 𝕜 ε m r‖ ≤ 3 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (anisotropicSummationScalarProjection_norm_apply_le 𝕜 hε m r)

theorem anisotropicSummationScalarProjection_full_tendsto {ε : ℝ} (hε : 0 < ε)
    (z : AnisotropicSpace (summationOperator 𝕜) ε) :
    Tendsto (fun m => anisotropicSummationScalarProjection 𝕜 ε m 0 z) atTop (𝓝 z) := by
  have ht := (toAnisotropic (summationOperator 𝕜) ε).continuous.tendsto
    (fromAnisotropic (summationOperator 𝕜) ε z) |>.comp
      (summationApproximationOperator_tendsto 𝕜 (fromAnisotropic (summationOperator 𝕜) ε z))
  simpa only [anisotropicSummationScalarProjection_apply, summationScalarProjection_zero,
    to_fromAnisotropic _ hε] using ht

end LindenstraussRetraction
