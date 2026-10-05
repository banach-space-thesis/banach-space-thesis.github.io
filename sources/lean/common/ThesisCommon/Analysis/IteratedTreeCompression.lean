import ThesisCommon.Analysis.IteratedSchauderBasis
import ThesisCommon.Analysis.NatTreeEmbedding
import ThesisCommon.Analysis.SchauderSumCompression
import ThesisCommon.Analysis.SchauderIsometricRange

/-! Every full infinitely splitting subtree gives an actual contractive
retraction pair on the iterated sum. This proves the isometric identification
of its closed terminal span, using the original symmetric norms at each level.
-/
noncomputable section
universe u v
namespace ThesisCommon
variable {𝕜 : Type u} [RCLike 𝕜]

theorem exists_iterated_tree_compression (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (h : ∀ F ∈ first :: tail, F.basis.HasSymmetricNorm)
    (f : NatTreeEmbedding (tail.length + 1)) :
    ∃ A B : (iteratedSchauderSum first tail).Carrier →L[𝕜]
        (iteratedSchauderSum first tail).Carrier,
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      (∀ t, B (iteratedBasisVector first tail t) = iteratedBasisVector first tail (f.map t)) ∧
      ∀ t x, iteratedBasisCoordinate first tail t (A x) =
        iteratedBasisCoordinate first tail (f.map t) x := by
  induction tail generalizing first with
  | nil =>
    obtain ⟨A, B, hAB, hA, hB, hBe, hAc⟩ :=
      first.basis.exists_subsequence_compression (h first (by simp)) f.1
    refine ⟨A, B, hAB, hA, hB, ?_, ?_⟩
    · intro t
      exact hBe (t 0)
    · intro t x
      exact hAc (t 0) x
  | cons next rest ih =>
    have htail : ∀ F ∈ next :: rest, F.basis.HasSymmetricNorm := by
      intro F hF
      exact h F (List.mem_cons_of_mem first hF)
    have hchild (i : ℕ) := ih next htail (f.2 i)
    choose A B hAB hA hB hBe hAc using hchild
    obtain ⟨R, E, hRE, hR, hE, hEe, hRc⟩ :=
      SchauderSum.exists_reindexed_compression (hb := first.oneUnconditional)
        (h first (by simp)) f.1 A B hAB hA hB
    refine ⟨R, E, hRE, hR, hE, ?_, ?_⟩
    · intro t
      change E (SchauderSum.single (b := first.basis) (hb := first.oneUnconditional)
        (t 0) (iteratedBasisVector next rest (Fin.tail t))) =
        SchauderSum.single (b := first.basis) (hb := first.oneUnconditional)
          (f.1 (t 0)) (iteratedBasisVector next rest ((f.2 (t 0)).map (Fin.tail t)))
      rw [hEe, hBe]
    · intro t x
      change SchauderSum first.basis first.oneUnconditional
        (iteratedSchauderSum next rest).Carrier at x
      change iteratedBasisCoordinate next rest (Fin.tail t) ((R x) (t 0)) =
        iteratedBasisCoordinate next rest ((f.2 (t 0)).map (Fin.tail t)) (x (f.1 (t 0)))
      rw [hRc, hAc]

/-- The closed span of the actual selected terminal vectors is isometrically
isomorphic to the original iterated space. No selection estimates are assumed. -/
theorem iterated_tree_span_isometric (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (h : ∀ F ∈ first :: tail, F.basis.HasSymmetricNorm)
    (f : NatTreeEmbedding (tail.length + 1)) :
    Nonempty ((iteratedSchauderSum first tail).Carrier ≃ₗᵢ[𝕜]
      (Submodule.span 𝕜 (Set.range (fun t => iteratedBasisVector first tail (f.map t)))).topologicalClosure) := by
  obtain ⟨A, B, hAB, hA, hB, hBe, _⟩ := exists_iterated_tree_compression first tail h f
  have hnorm := norm_eq_of_contractive_retraction A B hAB hA hB
  have heq : Set.range (fun k => B ((iteratedUnconditionalBasis first tail).val.vector k)) =
      Set.range (fun t => iteratedBasisVector first tail (f.map t)) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨natTupleEnumeration tail.length k, ?_⟩
      dsimp only
      rw [iteratedUnconditionalBasis_vector, hBe]
    · rintro ⟨t, rfl⟩
      refine ⟨(natTupleEnumeration tail.length).symm t, ?_⟩
      dsimp only
      rw [iteratedUnconditionalBasis_vector, Equiv.apply_symm_apply, hBe]
  have ht := (iteratedUnconditionalBasis first tail).val.nonempty_equiv_closed_span B hnorm
  rw [heq] at ht
  exact ht

end ThesisCommon
