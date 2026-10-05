import JLMS.CZeroSumFubini
import JLMS.CZeroSumOperators

/-!
# Replication of infinite Banach c₀ sums

The cardinal identity I × I ≃ I and Fubini identify an infinite constant
c₀ sum with its I-fold c₀ sum. Transporting this identity across a bounded
isomorphism is the successor-exponent step in Kislyakov Lemma 3.2.
-/

noncomputable section
namespace JLMS.CZeroSum
universe u v v' w
variable {𝕜 : Type w} [RCLike 𝕜]

def infiniteReplicateIsometry (I : Type u) [Infinite I] (X : Type v)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    CZeroSum 𝕜 (fun _ : I => X) ≃ₗᵢ[𝕜]
      CZeroSum 𝕜 (fun _ : I => CZeroSum 𝕜 (fun _ : I => X)) := by
  have hcard : Cardinal.mk (I × I) = Cardinal.mk I := by
    simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
      Cardinal.mul_eq_self (Cardinal.aleph0_le_mk I)
  let e : I × I ≃ I := Classical.choice (Cardinal.eq.mp hcard)
  exact (reindex (𝕜 := 𝕜) (E := fun _ : I => X) e).trans
    (prodIsometry (𝕜 := 𝕜) (E := fun _ _ : I => X)).symm

variable {I : Type u} [Infinite I] {X : Type v} {Y : Type v'}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

local instance replicationSumYGroup : NormedAddCommGroup (CZeroSum 𝕜 (fun _ : I => Y)) := inferInstance
local instance replicationSumYSpace : NormedSpace 𝕜 (CZeroSum 𝕜 (fun _ : I => Y)) := inferInstance
local instance replicationSumXGroup : NormedAddCommGroup (CZeroSum 𝕜 (fun _ : I => X)) := inferInstance
local instance replicationSumXSpace : NormedSpace 𝕜 (CZeroSum 𝕜 (fun _ : I => X)) := inferInstance
local instance replicationDoubleSumGroup :
    NormedAddCommGroup (CZeroSum 𝕜 (fun _ : I => CZeroSum 𝕜 (fun _ : I => Y))) := inferInstance
local instance replicationDoubleSumSpace :
    NormedSpace 𝕜 (CZeroSum 𝕜 (fun _ : I => CZeroSum 𝕜 (fun _ : I => Y))) := inferInstance

def replicationOfEquiv (e : X ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => Y)) :
    X ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => X) :=
  e.trans ((infiniteReplicateIsometry (𝕜 := 𝕜) I Y).toContinuousLinearEquiv.trans
    (congrRight (fun _ : I => e.symm) (norm_nonneg _) (norm_nonneg _)
      (fun _ => le_rfl) (fun _ => le_rfl)))

theorem norm_replicationOfEquiv_apply_le
    (e : X ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => Y)) (x : X) :
    ‖replicationOfEquiv e x‖ ≤
      (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) * ‖x‖ := by
  change ‖mapBounded (fun _ : I => e.symm.toContinuousLinearMap)
    (norm_nonneg _) (fun _ => le_rfl)
    (infiniteReplicateIsometry (𝕜 := 𝕜) I Y (e x))‖ ≤ _
  calc
    _ ≤ ‖e.symm.toContinuousLinearMap‖ *
        ‖infiniteReplicateIsometry (𝕜 := 𝕜) I Y (e x)‖ :=
      norm_mapBounded_le _ _ _ _
    _ = ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (e.toContinuousLinearMap.le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

theorem norm_replicationOfEquiv_symm_apply_le
    (e : X ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => Y))
    (x : CZeroSum 𝕜 (fun _ : I => X)) :
    ‖(replicationOfEquiv e).symm x‖ ≤
      (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) * ‖x‖ := by
  let y := mapBounded (fun _ : I => e.toContinuousLinearMap) (norm_nonneg _) (fun _ => le_rfl) x
  change ‖e.symm ((infiniteReplicateIsometry (𝕜 := 𝕜) I Y).symm y)‖ ≤ _
  calc
    _ ≤ ‖e.symm.toContinuousLinearMap‖ *
        ‖(infiniteReplicateIsometry (𝕜 := 𝕜) I Y).symm y‖ :=
      e.symm.toContinuousLinearMap.le_opNorm _
    _ = ‖e.symm.toContinuousLinearMap‖ * ‖y‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_mapBounded_le _ _ _ _) (norm_nonneg _)
    _ = _ := by ring

end JLMS.CZeroSum
