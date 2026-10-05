import ThesisCommon.Analysis.MixedInfinityRestriction
import ThesisCommon.Analysis.MixedInfinityCompression

/-! Transport the proved restricted matrix series through genuine coordinate
retractions. The global representation predicate is a conclusion of the
support restriction, not an assumption on the original operator. -/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

def HasInfinityMatrix
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) : Prop :=
  ∀ (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j : ℕ),
    HasSum (fun p : ℕ × ℕ => x p.1 p.2 * infinityEntry T i j p.1 p.2) (T x i j)

theorem infinity_compression_matrix_of_support (hs : b.HasSymmetricNorm)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) {M : Set ℕ}
    (hrep : ∀ (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)),
      (∀ r s, s ∉ M → x r s = 0) → ∀ i j,
      HasSum (fun p : ℕ × ℕ => x p.1 p.2 * infinityEntry T i j p.1 p.2) (T x i j))
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) (hm : ∀ i j, m i j ∈ M) :
    HasInfinityMatrix (((infinityRestrict hs n m).comp T).comp (infinityExtend hs n m)) := by
  intro x i j
  let y := infinityExtend (hb := hb) hs n m x
  have hy (r s : ℕ) (hsM : s ∉ M) : y r s = 0 := by
    apply infinityExtend_apply_off_range hs n m x (p := (r, s))
    rintro ⟨p, hp⟩
    apply hsM
    have hh : m p.1 p.2 = s := congrArg Prod.snd hp
    exact hh ▸ hm p.1 p.2
  have h := hrep y hy (n i) (m i j)
  have hoff (p : ℕ × ℕ) (hp : p ∉ Set.range (infinityPairEmbedding n m)) :
      y p.1 p.2 * infinityEntry T (n i) (m i j) p.1 p.2 = 0 := by
    rw [show y p.1 p.2 = 0 from infinityExtend_apply_off_range hs n m x hp, zero_mul]
  have hh := ((infinityPairEmbedding n m).injective.hasSum_iff hoff).mpr h
  simpa only [Function.comp_def, infinityPairEmbedding, Function.Embedding.coeFn_mk,
    y, infinityExtend_apply_image, infinityEntry_compression] using hh

theorem HasInfinityMatrix.compression (hs : b.HasSymmetricNorm)
    {T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)} (hT : HasInfinityMatrix T)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) :
    HasInfinityMatrix (((infinityRestrict hs n m).comp T).comp (infinityExtend hs n m)) :=
  infinity_compression_matrix_of_support hs T (M := Set.univ)
    (fun x _ i j => hT x i j) n m (fun _ _ => Set.mem_univ _)

theorem exists_infinity_matrix_compression (hs : b.HasSymmetricNorm)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) :
    ∃ A B : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
        SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞),
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        HasInfinityMatrix ((A.comp T).comp B) := by
  obtain ⟨M, _, hM, hrep⟩ := infinity_matrix_restriction T
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  let f : ℕ ↪ ℕ := (hM.natEmbedding M).trans (Function.Embedding.subtype M)
  exact ⟨infinityRestrict hs (Function.Embedding.refl ℕ) (fun _ => f),
    infinityExtend hs (Function.Embedding.refl ℕ) (fun _ => f),
    infinityRestrict_comp_extend hs _ _, norm_infinityRestrict_le hs _ _,
    norm_infinityExtend_le hs _ _, infinity_compression_matrix_of_support hs T hrep
      (Function.Embedding.refl ℕ) (fun _ => f) (fun _ j => (hM.natEmbedding M j).property)⟩

end SchauderSum
end ThesisCommon
