import ThesisCommon.Analysis.ScalarBlockEstimate

/-! Actual coordinate masks in a bounded product with varying coefficient
spaces. Disjoint bands give the finite scalar ℓ₁ estimate used in Lemma 5.10.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]

def boundedProductMask (I : Set ℕ) : lp E ∞ →L[𝕜] lp E ∞ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => if n ∈ I then x n else 0,
        memℓp_infty ⟨‖x‖, by
          rintro _ ⟨n, rfl⟩
          by_cases hn : n ∈ I
          · simpa only [if_pos hn] using lp.norm_apply_le_norm ENNReal.top_ne_zero x n
          · simpa only [if_neg hn, norm_zero] using norm_nonneg x⟩⟩
      map_add' := by
        intro x y; apply lp.ext; funext n
        change (if n ∈ I then x n + y n else 0) =
          (if n ∈ I then x n else 0) + (if n ∈ I then y n else 0)
        split_ifs <;> simp
      map_smul' := by
        intro a x; apply lp.ext; funext n
        change (if n ∈ I then a • x n else 0) = a • (if n ∈ I then x n else 0)
        split_ifs <;> simp }
    1 (fun x => by
      rw [one_mul]
      apply lp.norm_le_of_forall_le (norm_nonneg x)
      intro n
      change ‖if n ∈ I then x n else 0‖ ≤ ‖x‖
      split_ifs
      · exact lp.norm_apply_le_norm ENNReal.top_ne_zero x n
      · simpa only [norm_zero] using norm_nonneg x)

@[simp] theorem boundedProductMask_apply (I : Set ℕ) (x : lp E ∞) (n : ℕ) :
    boundedProductMask (𝕜 := 𝕜) I x n = if n ∈ I then x n else 0 := rfl

theorem norm_boundedProductMask_le (I : Set ℕ) :
    ‖boundedProductMask (𝕜 := 𝕜) (E := E) I‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem boundedProductMask_comp_of_subset {I J : Set ℕ} (h : I ⊆ J) :
    (boundedProductMask (𝕜 := 𝕜) (E := E) J).comp (boundedProductMask I) =
      boundedProductMask I := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  by_cases hn : n ∈ I
  · simp [hn, h hn]
  · simp [hn]

theorem boundedProductMask_functional_mono (f : lp E ∞ →L[𝕜] 𝕜)
    {I J : Set ℕ} (h : I ⊆ J) :
    ‖f.comp (boundedProductMask I)‖ ≤ ‖f.comp (boundedProductMask J)‖ := by
  have heq : f.comp (boundedProductMask I) =
      (f.comp (boundedProductMask J)).comp (boundedProductMask I) := by
    rw [ContinuousLinearMap.comp_assoc, boundedProductMask_comp_of_subset h]
  rw [heq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left
      (norm_boundedProductMask_le (𝕜 := 𝕜) (E := E) I) (norm_nonneg (f.comp (boundedProductMask J)))))

theorem boundedProductMask_disjoint_sum_norm_le {N : ℕ}
    (A : Fin N → Set ℕ) (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (x : Fin N → lp E ∞) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ‖∑ i, boundedProductMask (𝕜 := 𝕜) (A i) (x i)‖ ≤ 1 := by
  apply lp.norm_le_of_forall_le zero_le_one
  intro n
  simp only [lp.coeFn_sum, Finset.sum_apply, boundedProductMask_apply]
  by_cases h : ∃ i, n ∈ A i
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · rw [if_pos hi]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (x i) n).trans (hx i)
    · intro j _ hji
      exact if_neg (fun hj => Set.disjoint_left.mp (hA (Ne.symm hji)) hi hj)
    · simp
  · push_neg at h
    simp only [if_neg (h _), Finset.sum_const_zero, norm_zero, zero_le_one]

/-- A scalar functional becomes arbitrarily small on a whole infinite band.
The bands used here are disjoint infinite subsets of J; covering J is not
needed for the norm inequality in the manuscript's partition argument. -/
theorem boundedProductMask_scalar_small (f : lp E ∞ →L[𝕜] 𝕜)
    (J : Set ℕ) (hJ : J.Infinite) {ε : ℝ} (hε : 0 < ε) :
    ∃ I : Set ℕ, I ⊆ J ∧ I.Infinite ∧ ‖f.comp (boundedProductMask I)‖ ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖f‖ / ε)
  let a : ℕ ↪ ℕ := (hJ.natEmbedding J).trans (Function.Embedding.subtype J)
  let e (i : Fin N) : ℕ ↪ ℕ := (disjointCoordinateEmbedding i).trans a
  let A (i : Fin N) : Set ℕ := Set.range (e i)
  have hA : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro n ⟨s, hs⟩ ⟨t, ht⟩
    apply hij
    apply Fin.ext
    exact disjointCoordinateEmbedding_disjoint (a.injective (hs.trans ht.symm))
  obtain ⟨i, hi⟩ := exists_small_scalar_block
    (fun i : Fin N => boundedProductMask (𝕜 := 𝕜) (E := E) (A i))
    (norm_nonneg f) (boundedProductMask_disjoint_sum_norm_le A hA) f le_rfl
    (by simpa only [mul_one] using (div_lt_iff₀ hε).mp hN)
  refine ⟨A i, ?_, Set.infinite_range_of_injective (e i).injective, hi⟩
  rintro n ⟨k, rfl⟩
  exact (hJ.natEmbedding J (disjointCoordinateEmbedding i k)).property

theorem boundedProductMask_finite_scalar_small {ι : Type*}
    (f : ι → lp E ∞ →L[𝕜] 𝕜) (F : Finset ι) (J : Set ℕ) (hJ : J.Infinite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ I : Set ℕ, I ⊆ J ∧ I.Infinite ∧ ∀ i ∈ F, ‖(f i).comp (boundedProductMask I)‖ ≤ ε := by
  classical
  induction F using Finset.induction_on generalizing J with
  | empty => exact ⟨J, Set.Subset.rfl, hJ, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨K, hKJ, hK, hKF⟩ := ih J hJ
    obtain ⟨I, hIK, hI, hfi⟩ := boundedProductMask_scalar_small (f i) K hK hε
    refine ⟨I, hIK.trans hKJ, hI, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hfi
    · exact (boundedProductMask_functional_mono (f j) hIK).trans (hKF j hj)

end ThesisCommon
