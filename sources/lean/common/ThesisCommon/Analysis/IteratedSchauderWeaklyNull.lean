import ThesisCommon.Analysis.IteratedSchauderBasis
import ThesisCommon.Analysis.SchauderSumWeaklyNull

/-! The two vanishing matrix directions for CKL selection. The weak-null
row/fibre argument is applied recursively to the actual iterated spaces.
The column limit follows from the proved product Schauder expansion.
-/
noncomputable section
open Filter Topology
universe u v
namespace ThesisCommon
variable {𝕜 : Type u} [RCLike 𝕜]

theorem iteratedBasis_weakly_null (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (h : ∀ F ∈ first :: tail, F.basis.HasSymmetricNorm ∧ ¬ F.basis.EquivalentEllOne)
    (φ : (iteratedSchauderSum first tail).Carrier →L[𝕜] 𝕜) :
    Tendsto (fun k => φ ((iteratedUnconditionalBasis first tail).val.vector k))
      atTop (𝓝 0) := by
  induction tail generalizing first with
  | nil =>
    exact first.basis.weakly_null_of_not_equivalentEllOne
      (h first (by simp)).1 (h first (by simp)).2 φ
  | cons next rest ih =>
    have hfirst := h first (by simp)
    have htail : ∀ F ∈ next :: rest,
        F.basis.HasSymmetricNorm ∧ ¬ F.basis.EquivalentEllOne := by
      intro F hF
      exact h F (List.mem_cons_of_mem first hF)
    exact SchauderSum.product_weakly_null
      (iteratedUnconditionalBasis next rest).val
      (first.basis.weakly_null_of_not_equivalentEllOne hfirst.1 hfirst.2)
      (ih next htail) Nat.pairEquiv.symm φ

theorem iterated_matrix_row_tendsto_zero (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (h : ∀ F ∈ first :: tail, F.basis.HasSymmetricNorm ∧ ¬ F.basis.EquivalentEllOne)
    (T : (iteratedSchauderSum first tail).Carrier →L[𝕜]
      (iteratedSchauderSum first tail).Carrier) (t : Fin (tail.length + 1) → ℕ) :
    Tendsto (fun k => iteratedBasisCoordinate first tail t
      (T (iteratedBasisVector first tail (natTupleEnumeration tail.length k)))) atTop (𝓝 0) := by
  simpa only [ContinuousLinearMap.comp_apply, iteratedUnconditionalBasis_vector] using
    iteratedBasis_weakly_null first tail h ((iteratedBasisCoordinate first tail t).comp T)

theorem iterated_matrix_column_tendsto_zero (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (T : (iteratedSchauderSum first tail).Carrier →L[𝕜]
      (iteratedSchauderSum first tail).Carrier) (t : Fin (tail.length + 1) → ℕ) :
    Tendsto (fun k => iteratedBasisCoordinate first tail (natTupleEnumeration tail.length k)
      (T (iteratedBasisVector first tail t))) atTop (𝓝 0) := by
  simpa only [iteratedUnconditionalBasis_coord] using
    (iteratedUnconditionalBasis first tail).val.coord_tendsto_zero
      (T (iteratedBasisVector first tail t))

end ThesisCommon
