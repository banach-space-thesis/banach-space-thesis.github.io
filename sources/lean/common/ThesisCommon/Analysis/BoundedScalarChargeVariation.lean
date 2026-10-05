import ThesisCommon.Analysis.FilterConvergenceCriteria

/-! Finite disjoint-family variation bounds and deletion of a zero atom.
These are proved for actual finitely additive charges, without countable
additivity or any cardinal assumption. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.BoundedScalarCharge
variable {𝕜 Γ : Type*} [RCLike 𝕜] (μ : BoundedScalarCharge 𝕜 Γ)

theorem sum_norm_mem_variationValues {I : Type*} [Fintype I]
    (B : I → Set Γ) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    {A : Set Γ} (hBA : ∀ i, B i ⊆ A) :
    (∑ i, ‖μ (B i)‖) ∈ μ.variationValues A := by
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun i => B (e i), ?_, fun i => hBA (e i), ?_⟩
  · intro i j hij
    exact hB (fun h => hij (e.injective h))
  · exact (e.sum_comp (fun i => ‖μ (B i)‖)).symm

theorem variation_union_ge {A B : Set Γ} (hAB : Disjoint A B) :
    μ.variation A + μ.variation B ≤ μ.variation (A ∪ B) := by
  have hfinite : ∀ r ∈ μ.variationValues A, ∀ s ∈ μ.variationValues B,
      r + s ≤ μ.variation (A ∪ B) := by
    rintro r ⟨n, C, hC, hCA, rfl⟩ s ⟨m, D, hD, hDB, rfl⟩
    let E : Fin n ⊕ Fin m → Set Γ := Sum.elim C D
    have hE : Pairwise (fun i j => Disjoint (E i) (E j)) := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact hC (fun h => hij (congrArg Sum.inl h))
        | inr j => exact hAB.mono (hCA i) (hDB j)
      | inr i =>
        cases j with
        | inl j => exact hAB.symm.mono (hDB i) (hCA j)
        | inr j => exact hD (fun h => hij (congrArg Sum.inr h))
    have hEA : ∀ i, E i ⊆ A ∪ B := by
      intro i
      cases i with
      | inl i => exact (hCA i).trans Set.subset_union_left
      | inr i => exact (hDB i).trans Set.subset_union_right
    have ht := le_csSup (μ.variationValues_bddAbove (A ∪ B))
      (μ.sum_norm_mem_variationValues E hE hEA)
    simpa only [Fintype.sum_sum_type, E, Sum.elim_inl, Sum.elim_inr] using ht
  have hr : ∀ r ∈ μ.variationValues A, r + μ.variation B ≤ μ.variation (A ∪ B) := by
    intro r hr
    have hb : μ.variation B ≤ μ.variation (A ∪ B) - r := by
      apply csSup_le (μ.variationValues_nonempty B)
      intro s hs
      linarith [hfinite r hr s hs]
    linarith
  have ha : μ.variation A ≤ μ.variation (A ∪ B) - μ.variation B := by
    apply csSup_le (μ.variationValues_nonempty A)
    intro r h
    linarith [hr r h]
  linarith

theorem sum_variation_le {n : ℕ} (B : Fin n → Set Γ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    ∑ i, μ.variation (B i) ≤ μ.variation Set.univ := by
  classical
  have hsum (s : Finset (Fin n)) :
      ∑ i ∈ s, μ.variation (B i) ≤ μ.variation (⋃ i ∈ s, B i) := by
    induction s using Finset.induction_on with
    | empty => simpa using μ.variation_nonneg ∅
    | @insert i s hi ih =>
      have hd : Disjoint (B i) (⋃ j ∈ s, B j) := by
        apply Set.disjoint_iUnion₂_right.mpr
        intro j hj
        exact hB (fun h => hi (h ▸ hj))
      have heq : (⋃ j ∈ insert i s, B j) = B i ∪ ⋃ j ∈ s, B j := by
        ext γ
        simp only [Set.mem_iUnion, Finset.mem_insert]
        aesop
      rw [Finset.sum_insert hi, heq]
      exact (add_le_add_left ih _).trans (μ.variation_union_ge hd)
  exact (hsum Finset.univ).trans (μ.variation_mono (Set.subset_univ _))

theorem apply_sdiff_singleton {a : Γ} (h : μ {a} = 0) (A : Set Γ) :
    μ (A \ {a}) = μ A := by
  classical
  by_cases ha : a ∈ A
  · have hd : Disjoint (A \ {a}) {a} := by
      apply Set.disjoint_left.mpr
      intro x hx hxa
      exact hx.2 hxa
    have heq : (A \ {a}) ∪ {a} = A := by
      ext x
      by_cases hx : x = a <;> simp [hx, ha]
    have hm := μ.map_union (A \ {a}) {a} hd
    rw [heq, h, add_zero] at hm
    exact hm.symm
  · have heq : A \ {a} = A := by
      ext x
      by_cases hx : x = a <;> simp [hx, ha]
    rw [heq]

theorem variation_sdiff_singleton {a : Γ} (h : μ {a} = 0) (A : Set Γ) :
    μ.variation (A \ {a}) = μ.variation A := by
  apply le_antisymm (μ.variation_mono Set.diff_subset)
  apply csSup_le (μ.variationValues_nonempty A)
  rintro r ⟨n, B, hB, hBA, rfl⟩
  apply le_csSup (μ.variationValues_bddAbove (A \ {a}))
  refine ⟨n, fun i => B i \ {a}, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hB hij).mono Set.diff_subset Set.diff_subset
  · intro i x hx
    exact ⟨hBA i hx.1, hx.2⟩
  · simp only [μ.apply_sdiff_singleton h]

end ThesisCommon.BoundedScalarCharge
