import SurveyStatements.P5OperatorReductionCountableBudgets
import SurveyStatements.P5BiTreeStabilizationGeometry
import SurveyStatements.P5GeneralMixedErrorIndexing

/-! Positive finite-selection tolerances retain their weighted total after
reindexing by the genuine canonical Haar coordinates. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support

def stripHeapIndices (q : GeneralMixedStripIndex) : ℕ × ℕ :=
  (lpHaarHeapIndex q.val.1.1 q.val.1.2, lpHaarHeapIndex q.val.2.1 q.val.2.2)

theorem stripHeapIndices_injective : Function.Injective stripHeapIndices := by
  intro q r h
  apply Subtype.ext
  apply Prod.ext
  · apply BiTree.heapIndex_injective
    exact congrArg Prod.fst h
  · apply BiTree.heapIndex_injective
    exact congrArg Prod.snd h

def nuclearHeapIndices (q : GeneralMixedNuclearIndex) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((lpHaarHeapIndex q.val.1.1.1 q.val.1.1.2,
    lpHaarHeapIndex q.val.1.2.1 q.val.1.2.2),
   (lpHaarHeapIndex q.val.2.1.1 q.val.2.1.2,
    lpHaarHeapIndex q.val.2.2.1 q.val.2.2.2))

theorem nuclearHeapIndices_injective : Function.Injective nuclearHeapIndices := by
  intro q r h
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · apply BiTree.heapIndex_injective
      exact congrArg (fun x => x.1.1) h
    · apply BiTree.heapIndex_injective
      exact congrArg (fun x => x.1.2) h
  · apply Prod.ext
    · apply BiTree.heapIndex_injective
      exact congrArg (fun x => x.2.1) h
    · apply BiTree.heapIndex_injective
      exact congrArg (fun x => x.2.2) h

theorem exists_positive_reindexed_error_budget {I J : Type*} [Countable I]
    (C : I → ℝ) (hC : ∀ i, 0 ≤ C i) {ε : ℝ} (hε : 0 < ε)
    (f : J → I) (hf : Function.Injective f) :
    ∃ δ : I → ℝ, (∀ i, 0 < δ i) ∧
      Summable (fun j => C (f j) * δ (f j)) ∧
      (∑' j, C (f j) * δ (f j)) ≤ ε / 2 := by
  obtain ⟨δ, hδ, _, hsum, _, htotal⟩ :=
    exists_positive_countable_error_budget C hC hε
  refine ⟨δ, hδ, hsum.comp_injective hf, ?_⟩
  exact (Summable.tsum_le_tsum_of_inj f hf
    (fun i _ => mul_nonneg (hC i) (hδ i).le)
    (fun _ => le_rfl) (hsum.comp_injective hf) hsum).trans htotal

end SurveyStatements.P5OperatorReduction
