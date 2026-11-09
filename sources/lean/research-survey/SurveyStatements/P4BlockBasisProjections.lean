import SurveyStatements.P4BlockBasisCoordinates

/-! Each ordered prefix consists of a contractive full-block projection and
one uniformly bounded finite-block prefix. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

open Set Finset Filter Topology Module
open scoped BigOperators ENNReal

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {Z : Type v} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable (D : ContractiveFiniteDecomposition 𝕜 Z)
variable (G : ∀ n, FiniteBasisExtension 𝕜 (D.Block n))

lemma finiteBasisPrefix_basis {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {d : ℕ} (b : Basis (Fin d) 𝕜 E)
    (k : Fin (d + 1)) (i : Fin d) :
    finiteBasisPrefix b k (b i) = if i.val < k.val then b i else 0 := by
  classical
  simp only [finiteBasisPrefix, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap',
    Basis.coord_apply, Basis.repr_self]
  by_cases hi : i.val < k.val
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · simp [hi]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      exact hi (Finset.mem_filter.mp hj).2
    simp [hji]

lemma orderedBasisProjection_basis_all {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : Set ℕ}
    (b : I → E) (φ : I → StrongDual 𝕜 E)
    (hbi : ∀ i j, φ i (b j) = if i = j then 1 else 0) (i : I) (N : ℕ) :
    orderedBasisProjection b φ N (b i) = if i.val < N then b i else 0 := by
  classical
  by_cases hi : i.val < N
  · rw [if_pos hi]
    exact orderedBasisProjection_basis b φ hbi i hi
  · rw [if_neg hi, orderedBasisProjection_apply]
    unfold schauderPartialSum
    apply Finset.sum_eq_zero
    intro n hn
    by_cases hnI : n ∈ I
    · have hne : (⟨n, hnI⟩ : I) ≠ i := by
        intro h
        have heq := congrArg Subtype.val h
        exact hi (heq ▸ Finset.mem_range.mp hn)
      simp [hnI, hbi, hne]
    · simp [hnI]

set_option maxHeartbeats 3000000 in
lemma blockBasisFullProjection_injection (N m : ℕ) (x : BlockBasisBlock D G m) :
    blockBasisFullProjection D G N (blockBasisInjection D G m x) =
      if m < N then blockBasisInjection D G m x else 0 := by
  classical
  simp only [blockBasisFullProjection, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  by_cases hm : m < N
  · rw [if_pos hm, Finset.sum_eq_single m]
    · exact congrArg (blockBasisInjection D G m) (blockBasisCoordinate_injection D G m x)
    · intro n hn hnm
      exact (congrArg (blockBasisInjection D G n)
        (blockBasisCoordinate_injection_of_ne D G hnm x)).trans
          (blockBasisInjection D G n).map_zero
    · exact fun h => False.elim (h (Finset.mem_range.mpr hm))
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro n hn
    have hnm : n ≠ m := by
      intro h
      exact hm (h ▸ Finset.mem_range.mp hn)
    exact (congrArg (blockBasisInjection D G n)
      (blockBasisCoordinate_injection_of_ne D G hnm x)).trans
        (blockBasisInjection D G n).map_zero

def blockBasisPartialProjection (n : ℕ) (k : Fin ((G n).length + 1)) :
    BlockBasisSpace D G →L[𝕜] BlockBasisSpace D G :=
  (blockBasisInjection D G n).comp
    ((finiteBasisPrefix (G n).complementBasis k).comp (blockBasisCoordinate D G n))

lemma norm_blockBasisPartialProjection_le (n : ℕ) (k : Fin ((G n).length + 1)) :
    ‖blockBasisPartialProjection D G n k‖ ≤ 18 := by
  unfold blockBasisPartialProjection
  calc
    _ ≤ ‖blockBasisInjection D G n‖ *
        ‖(finiteBasisPrefix (G n).complementBasis k).comp (blockBasisCoordinate D G n)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (9 * 2) := by
      have hc : ‖(finiteBasisPrefix (G n).complementBasis k).comp
          (blockBasisCoordinate D G n)‖ ≤ 9 * 2 :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul ((G n).norm_complementBasis_prefix_le k)
            (norm_blockBasisCoordinate_le D G n)
            (ContinuousLinearMap.opNorm_nonneg (blockBasisCoordinate D G n)) (by norm_num))
      exact mul_le_mul (norm_blockBasisInjection_le D G n) hc
        (ContinuousLinearMap.opNorm_nonneg _) (by norm_num)
    _ = 18 := by norm_num

set_option maxHeartbeats 3000000 in
lemma blockBasisPartialProjection_basis (n : ℕ) (k : Fin ((G n).length + 1))
    (i : Σ m, Fin (G m).length) :
    blockBasisPartialProjection D G n k
        (blockBasisVector D G (blockEncode (fun m => (G m).length) i)) =
      if i.1 = n then
        if i.2.val < k.val then
          blockBasisVector D G (blockEncode (fun m => (G m).length) i) else 0
      else 0 := by
  classical
  rcases i with ⟨m, i⟩
  simp only [blockBasisPartialProjection, ContinuousLinearMap.comp_apply,
    blockBasisVector_encode]
  by_cases hmn : m = n
  · subst m
    rw [blockBasisCoordinate_injection, finiteBasisPrefix_basis]
    rw [if_pos rfl]
    by_cases hi : i.val < k.val
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi]
      exact (blockBasisInjection D G n).map_zero
  · rw [if_neg hmn]
    exact (congrArg (fun y => blockBasisInjection D G n
      (finiteBasisPrefix (G n).complementBasis k y))
        (blockBasisCoordinate_injection_of_ne D G (Ne.symm hmn)
          ((G m).complementBasis i))).trans (by
            rw [(finiteBasisPrefix (G n).complementBasis k).map_zero,
              (blockBasisInjection D G n).map_zero])

lemma blockBasis_maps_eq_of_basis (A B : BlockBasisSpace D G →L[𝕜] BlockBasisSpace D G)
    (h : ∀ i, A (blockBasisVector D G i) = B (blockBasisVector D G i)) : A = B := by
  have hr : Set.EqOn A B (range (blockBasisVector D G)) := by
    rintro x ⟨i, rfl⟩
    exact h i
  have hs : Set.EqOn A B (Submodule.span 𝕜 (range (blockBasisVector D G))) :=
    LinearMap.eqOn_span' (R := 𝕜) hr
  apply ContinuousLinearMap.ext
  intro x
  exact hs.closure A.continuous B.continuous (blockBasis_span_dense D G x)

lemma blockBasisIndicatorIdentity (d : ℕ → ℕ) (m n : ℕ)
    (i : Fin (d m)) (j : Fin (d n)) {A : Type w} [AddZeroClass A] (x : A) :
    (if (blockEncode d ⟨m, i⟩).val < (blockEncode d ⟨n, j⟩).val then x else 0) =
      (if m < n then x else 0) +
        (if m = n then (if i.val < j.val then x else 0) else 0) := by
  classical
  by_cases hmn : m = n
  · subst m
    have henc : (blockEncode d ⟨n, i⟩).val <
        (blockEncode d ⟨n, j⟩).val ↔ i.val < j.val :=
      Nat.add_lt_add_iff_left
    rw [if_neg (lt_irrefl n), if_pos (rfl : n = n), zero_add]
    by_cases hij : i.val < j.val
    · rw [if_pos (henc.mpr hij), if_pos hij]
    · rw [if_neg (fun h => hij (henc.mp h)), if_neg hij]
  · rcases lt_or_gt_of_ne hmn with hmnlt | hnmgt
    · have henc := (blockEncode_lt_offset_iff d ⟨m, i⟩ n).2 hmnlt
      have hless : (blockEncode d ⟨m, i⟩).val < (blockEncode d ⟨n, j⟩).val := by
        change _ < blockOffset d n + j.val
        omega
      rw [if_pos hless, if_pos hmnlt, if_neg hmn, add_zero]
    · have hmono := blockOffset_monotone d (Nat.succ_le_of_lt hnmgt)
      rw [blockOffset_succ] at hmono
      have hnless : ¬ (blockEncode d ⟨m, i⟩).val < (blockEncode d ⟨n, j⟩).val := by
        change ¬ blockOffset d m + i.val < blockOffset d n + j.val
        have hj := j.isLt
        omega
      rw [if_neg hnless, if_neg (Nat.not_lt.mpr (Nat.le_of_lt hnmgt)),
        if_neg hmn, zero_add]

set_option maxHeartbeats 3000000 in
lemma blockBasis_orderedProjection_encode (j : Σ n, Fin (G n).length) :
    orderedBasisProjection (blockBasisVector D G) (blockBasisFunctional D G)
        (blockEncode (fun n => (G n).length) j).val =
      blockBasisFullProjection D G j.1 +
        blockBasisPartialProjection D G j.1 ⟨j.2.val, by omega⟩ := by
  classical
  rcases j with ⟨n, j⟩
  apply blockBasis_maps_eq_of_basis D G
  intro i
  obtain ⟨⟨m, i⟩, rfl⟩ := blockEncode_surjective (fun n => (G n).length) i
  rw [orderedBasisProjection_basis_all _ _ (blockBasis_biorthogonal D G),
    ContinuousLinearMap.add_apply, blockBasisPartialProjection_basis,
    blockBasisVector_encode, blockBasisFullProjection_injection]
  exact blockBasisIndicatorIdentity (fun n => (G n).length) m n i j
    (blockBasisInjection D G m ((G m).complementBasis i))

theorem norm_blockBasis_orderedProjection_le (N : ℕ) :
    ‖orderedBasisProjection (blockBasisVector D G) (blockBasisFunctional D G) N‖ ≤ 19 := by
  classical
  by_cases hN : N ∈ blockIndexSet (fun n => (G n).length)
  · obtain ⟨j, hj⟩ := blockEncode_surjective (fun n => (G n).length) ⟨N, hN⟩
    have hv := congrArg Subtype.val hj
    change (blockEncode (fun n => (G n).length) j).val = N at hv
    rw [← hv, blockBasis_orderedProjection_encode]
    exact (norm_add_le _ _).trans (by linarith
      [norm_blockBasisFullProjection_le D G j.1,
        norm_blockBasisPartialProjection_le D G j.1 ⟨j.2.val, by omega⟩])
  · have heq : orderedBasisProjection (blockBasisVector D G) (blockBasisFunctional D G) N =
        ContinuousLinearMap.id 𝕜 (BlockBasisSpace D G) := by
      apply blockBasis_maps_eq_of_basis D G
      intro i
      have hi : i.val < N := by
        by_contra h
        exact hN ((blockIndexSet_isLowerSet (fun n => (G n).length))
          (Nat.le_of_not_gt h) i.property)
      exact orderedBasisProjection_basis _ _ (blockBasis_biorthogonal D G) i hi
    rw [heq]
    exact ContinuousLinearMap.norm_id_le.trans (by norm_num)

theorem blockBasis_isSchauder : IsSchauderBasis 𝕜 (blockBasisVector D G) :=
  isSchauderBasis_of_biorthogonal_uniform_bound
    (blockIndexSet_isLowerSet (fun n => (G n).length))
    (blockBasisVector D G) (blockBasisFunctional D G) (blockBasis_biorthogonal D G)
    19 (by norm_num) (norm_blockBasis_orderedProjection_le D G) (blockBasis_span_dense D G)

theorem blockBasisSpace_hasSchauderBasis : HasSchauderBasis 𝕜 (BlockBasisSpace D G) :=
  ⟨_, blockBasisVector D G, blockBasis_isSchauder D G⟩

end SurveyStatements.P4
