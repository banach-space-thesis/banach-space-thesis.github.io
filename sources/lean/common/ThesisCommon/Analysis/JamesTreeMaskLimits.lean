import ThesisCommon.Analysis.JamesTreeMasks

/-! Exhausting contractive coordinate masks converge strongly on the genuine
completion. Nonempty masks have norm exactly one, witnessed by a unit vector. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTreeMask_fix_dense (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A)
    (a : JamesTreePreSpace 𝕜 p S) (ha : ∀ t ∉ A, a t = 0) :
    jamesTreeMask A hA (jamesTreeDenseEmbedding 𝕜 p S a) = jamesTreeDenseEmbedding 𝕜 p S a := by
  rw [jamesTreeMask_dense]
  apply congrArg (jamesTreeDenseEmbedding 𝕜 p S)
  ext t
  by_cases ht : t ∈ A
  · simp only [JamesTreePreSpace.mask_apply, if_pos ht]
  · simp only [JamesTreePreSpace.mask_apply, if_neg ht, ha t ht]

theorem norm_jamesTreeMask_eq_one (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A)
    (hne : A.Nonempty) : ‖jamesTreeMask (𝕜 := 𝕜) (p := p) A hA‖ = 1 := by
  obtain ⟨t, ht⟩ := hne
  let a : JamesTreePreSpace 𝕜 p S := JamesTreePreSpace.single t 1
  have ha : ∀ u ∉ A, a u = 0 := by
    intro u hu
    have htu : t ≠ u := fun h => hu (h ▸ ht)
    simp only [a, JamesTreePreSpace.single_apply, if_neg htu]
  have hx : ‖jamesTreeDenseEmbedding 𝕜 p S a‖ = 1 := by simp [a]
  apply le_antisymm (norm_jamesTreeMask_le A hA)
  have h := (jamesTreeMask (𝕜 := 𝕜) (p := p) A hA).le_opNorm
    (jamesTreeDenseEmbedding 𝕜 p S a)
  simpa only [jamesTreeMask_fix_dense A hA a ha, hx, mul_one] using h

theorem jamesTreeMask_tendsto (A : ℕ → Set DyadicTreeNode)
    (hA : ∀ n, JamesTreeMaskClosed S (A n))
    (hcover : ∀ t, ∀ᶠ n in atTop, t ∈ A n) (x : SegmentJamesTreeSpace 𝕜 p S) :
    Tendsto (fun n => jamesTreeMask (A n) (hA n) x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨a, ha⟩ := (jamesTreeDenseEmbedding_denseRange 𝕜 p S).exists_dist_lt x (half_pos hε)
  have hevent : ∀ᶠ n in atTop,
      ∀ t ∈ a.coefficients.support, t ∈ A n :=
    (Filter.eventually_all_finset _).mpr (fun t _ => hcover t)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, ?_⟩
  intro n hn
  have hfix := jamesTreeMask_fix_dense (A n) (hA n) a (by
    intro t ht
    apply Finsupp.notMem_support_iff.mp
    exact fun hts => ht (hN n hn t hts))
  calc
    dist (jamesTreeMask (A n) (hA n) x) x ≤
        dist (jamesTreeMask (A n) (hA n) x) (jamesTreeDenseEmbedding 𝕜 p S a) +
          dist (jamesTreeDenseEmbedding 𝕜 p S a) x := dist_triangle _ _ _
    _ ≤ dist x (jamesTreeDenseEmbedding 𝕜 p S a) +
          dist (jamesTreeDenseEmbedding 𝕜 p S a) x := by
      apply add_le_add_right
      calc
        _ = dist (jamesTreeMask (A n) (hA n) x)
            (jamesTreeMask (A n) (hA n) (jamesTreeDenseEmbedding 𝕜 p S a)) := by rw [hfix]
        _ ≤ _ := by
          rw [dist_eq_norm, dist_eq_norm, ← map_sub]
          exact jamesTreeMask_norm_le (A n) (hA n) (x - jamesTreeDenseEmbedding 𝕜 p S a)
    _ < ε := by rw [dist_comm (jamesTreeDenseEmbedding 𝕜 p S a) x]; linarith

end ThesisCommon
