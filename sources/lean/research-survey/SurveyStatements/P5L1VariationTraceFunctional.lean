import SurveyStatements.P5L1VariationOriginalLocalTrace

/-! The paper's local trace as an actual bounded linear functional on
operators on the mean-zero L1 space. Its value is determined by the full
sequence of the paper's normalized descendant averages. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support
attribute [local irreducible] intervalLpMeanZeroSubmodule

local instance (priority := 2000) meanZeroOperatorsNormed (𝕜 : Type*) [RCLike 𝕜] :
    NormedAddCommGroup (MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance (priority := 2000) meanZeroOperatorsSeminormed (𝕜 : Type*) [RCLike 𝕜] :
    SeminormedAddCommGroup (MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :=
  (meanZeroOperatorsNormed 𝕜).toSeminormedAddCommGroup

local instance (priority := 2000) meanZeroOperatorsSpace (𝕜 : Type*) [RCLike 𝕜] :
    NormedSpace 𝕜 (MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :=
  ContinuousLinearMap.toNormedSpace

theorem haarOperatorDiagonal_meanZero_add (𝕜 : Type*) [RCLike 𝕜]
    (R Q : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (n : ℕ) (k : Fin (2 ^ n)) :
    haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 (R + Q)) n k =
      haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n k +
        haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 Q) n k := by
  simp only [haarOperatorDiagonal_on_meanZero, ContinuousLinearMap.add_apply,
    Submodule.coe_add, map_add]

theorem haarOperatorDiagonal_meanZero_smul (𝕜 : Type*) [RCLike 𝕜]
    (c : 𝕜) (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (n : ℕ) (k : Fin (2 ^ n)) :
    haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 (c • R)) n k =
      c * haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n k := by
  simp only [haarOperatorDiagonal_on_meanZero, ContinuousLinearMap.smul_apply,
    Submodule.coe_smul, map_smul, smul_eq_mul]

theorem localLevelAverage_add (𝕜 : Type*) [RCLike 𝕜]
    (R Q : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (n r : ℕ) (hr : r ≤ n) (root : Fin (2 ^ r)) :
    localLevelAverage 𝕜 (R + Q) n r hr root =
      localLevelAverage 𝕜 R n r hr root + localLevelAverage 𝕜 Q n r hr root := by
  simp only [localLevelAverage, haarOperatorDiagonal_meanZero_add,
    Finset.sum_add_distrib, mul_add]

theorem localLevelAverage_smul (𝕜 : Type*) [RCLike 𝕜]
    (c : 𝕜) (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (n r : ℕ) (hr : r ≤ n) (root : Fin (2 ^ r)) :
    localLevelAverage 𝕜 (c • R) n r hr root = c * localLevelAverage 𝕜 R n r hr root := by
  simp only [localLevelAverage, haarOperatorDiagonal_meanZero_smul, ← Finset.mul_sum]
  ring

theorem arbitraryLocalTraceValue_average_tendsto (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ) (root : Fin (2 ^ r)) :
    Tendsto (fun j => localLevelAverage 𝕜 R (r + j) r (by omega) root) atTop
      (𝓝 (arbitraryLocalTraceValue 𝕜 R r root)) :=
  (Classical.choose_spec (arbitrary_operator_local_average_limit 𝕜 R r root).2.2).2

theorem arbitraryLocalTraceValue_add (𝕜 : Type*) [RCLike 𝕜]
    (R Q : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ) (root : Fin (2 ^ r)) :
    arbitraryLocalTraceValue 𝕜 (R + Q) r root =
      arbitraryLocalTraceValue 𝕜 R r root + arbitraryLocalTraceValue 𝕜 Q r root := by
  apply tendsto_nhds_unique (arbitraryLocalTraceValue_average_tendsto 𝕜 (R + Q) r root)
  simpa only [localLevelAverage_add] using
    (arbitraryLocalTraceValue_average_tendsto 𝕜 R r root).add
      (arbitraryLocalTraceValue_average_tendsto 𝕜 Q r root)

theorem arbitraryLocalTraceValue_smul (𝕜 : Type*) [RCLike 𝕜]
    (c : 𝕜) (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ) (root : Fin (2 ^ r)) :
    arbitraryLocalTraceValue 𝕜 (c • R) r root = c * arbitraryLocalTraceValue 𝕜 R r root := by
  apply tendsto_nhds_unique (arbitraryLocalTraceValue_average_tendsto 𝕜 (c • R) r root)
  simpa only [localLevelAverage_smul] using
    (arbitraryLocalTraceValue_average_tendsto 𝕜 R r root).const_mul c

def cellTraceFunctional (𝕜 : Type*) [RCLike 𝕜] (r : ℕ) (root : Fin (2 ^ r)) :
    (MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    ({ toFun := fun R => arbitraryLocalTraceValue 𝕜 R r root
       map_add' := fun R Q => arbitraryLocalTraceValue_add 𝕜 R Q r root
       map_smul' := fun c R => by
         simpa only [RingHom.id_apply, smul_eq_mul] using
           arbitraryLocalTraceValue_smul 𝕜 c R r root } :
        (MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) →ₗ[𝕜] 𝕜)
    2 (fun R => arbitraryLocalTraceValue_norm_le 𝕜 R r root)

theorem norm_cellTraceFunctional_le (𝕜 : Type*) [RCLike 𝕜]
    (r : ℕ) (root : Fin (2 ^ r)) : ‖cellTraceFunctional 𝕜 r root‖ ≤ 2 := by
  unfold cellTraceFunctional
  exact LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem cellTraceFunctional_apply (𝕜 : Type*) [RCLike 𝕜]
    (r : ℕ) (root : Fin (2 ^ r))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :
    cellTraceFunctional 𝕜 r root R = arbitraryLocalTraceValue 𝕜 R r root := rfl

attribute [local irreducible] cellTraceFunctional

def localTraceFunctional (𝕜 : Type*) [RCLike 𝕜]
    (r : ℕ) (S : Finset (Fin (2 ^ r))) :
    (MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) →L[𝕜] 𝕜 :=
  (S.card : 𝕜)⁻¹ • ∑ root ∈ S, cellTraceFunctional 𝕜 r root

theorem localTraceFunctional_apply (𝕜 : Type*) [RCLike 𝕜]
    (r : ℕ) (S : Finset (Fin (2 ^ r)))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :
    localTraceFunctional 𝕜 r S R =
      (S.card : 𝕜)⁻¹ * ∑ root ∈ S, arbitraryLocalTraceValue 𝕜 R r root := by
  simp only [localTraceFunctional, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, cellTraceFunctional_apply, smul_eq_mul]

theorem norm_localTraceFunctional_le (𝕜 : Type*) [RCLike 𝕜]
    (r : ℕ) (S : Finset (Fin (2 ^ r))) : ‖localTraceFunctional 𝕜 r S‖ ≤ 2 := by
  by_cases hS : S.Nonempty
  · have hc : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
    calc
      _ = (S.card : ℝ)⁻¹ * ‖∑ root ∈ S, cellTraceFunctional 𝕜 r root‖ := by
        simp [localTraceFunctional, norm_smul, norm_inv]
      _ ≤ (S.card : ℝ)⁻¹ * ∑ root ∈ S, ‖cellTraceFunctional 𝕜 r root‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (S.card : ℝ)⁻¹ * ∑ _root ∈ S, (2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun root _ => norm_cellTraceFunctional_le 𝕜 r root))
          (by positivity)
      _ = 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [this, localTraceFunctional]

theorem localTraceFunctional_tendsto (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (r : ℕ) (S : Finset (Fin (2 ^ r))) :
    Tendsto (equalDyadicLevelAverage 𝕜 R r S) atTop
      (𝓝 (localTraceFunctional 𝕜 r S R)) := by
  rw [localTraceFunctional_apply]
  have h := tendsto_finset_sum S (fun root _ =>
    arbitraryLocalTraceValue_average_tendsto 𝕜 R r root)
  simpa only [equalDyadicLevelAverage] using h.const_mul ((S.card : 𝕜)⁻¹)

end SurveyStatements.P5L1Variation
