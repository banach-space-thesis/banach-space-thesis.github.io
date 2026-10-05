import JLMS.CZeroSumProduct
import JLMS.CZeroSumOperators
import JLMS.CZeroSumFubini
import JLMS.OrdinalSpaceSumAbsorption

/-!
# Replication from a family of absorbed blocks

If E is a c₀ sum of blocks F_b, is stable under B-fold replication,
and uniformly absorbs I copies of each block, then E is stable under
I-fold replication. This upgrades the cofinality-sized decomposition
in Kislyakov Lemma 3.3 to replication by the full cardinal.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace JLMS
universe u u' v v' w
variable {𝕜 : Type w} [RCLike 𝕜]

local instance blockReplicationSumGroup {J : Type*} (F : J → Type*)
    [∀ j, NormedAddCommGroup (F j)] [∀ j, NormedSpace 𝕜 (F j)] :
    NormedAddCommGroup (CZeroSum 𝕜 F) := inferInstance
local instance blockReplicationSumSpace {J : Type*} (F : J → Type*)
    [∀ j, NormedAddCommGroup (F j)] [∀ j, NormedSpace 𝕜 (F j)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 F) := inferInstance

/-- Uniform absorption of the individual blocks upgrades replication of E. -/
theorem nonempty_cZeroSum_replicationFromBlocks
    {B : Type u} (I : Type u') [Infinite I] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : B → Type v') [∀ b, NormedAddCommGroup (F b)] [∀ b, NormedSpace 𝕜 (F b)]
    (r : E ≃L[𝕜] CZeroSum 𝕜 F)
    (s : E ≃L[𝕜] CZeroSum 𝕜 (fun _ : B => E))
    {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ b, ∃ e : E ≃L[𝕜] E × CZeroSum 𝕜 (fun _ : I => F b),
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ K) :
    Nonempty (E ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => E)) := by
  obtain ⟨t, _ht⟩ := CZeroSum.exists_congrRight_of_distortion
    (𝕜 := 𝕜) (I := B) (E := fun _ => E)
    (F := fun b => E × CZeroSum 𝕜 (fun _ : I => F b)) hK he
  let q : CZeroSum 𝕜 (fun b => CZeroSum 𝕜 (fun _ : I => F b)) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : I => E) :=
    (CZeroSum.commuteIsometry (𝕜 := 𝕜) (E := fun b (_ : I) => F b)).toContinuousLinearEquiv.trans
      (CZeroSum.congrRight (fun _ : I => r.symm) (norm_nonneg _) (norm_nonneg _)
        (fun _ => le_rfl) (fun _ => le_rfl))
  exact ⟨s.trans (t.trans (CZeroSum.productIsometry.toContinuousLinearEquiv.trans
    ((s.symm.prodCongr q).trans
      (cZeroSumInfiniteHeadIsometry (𝕜 := 𝕜) I E).symm.toContinuousLinearEquiv)))⟩

end JLMS
