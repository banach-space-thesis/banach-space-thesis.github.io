import Sigma.ConstructionState

/-! All four construction invariants persist through directed unions of stages. -/
noncomputable section
open Set ThesisCommon
namespace SigmaNonprimarity

theorem ThreeLevelChoice.Nonseparated.directed_limit {K : Type} [Nonempty K]
    {μ : AtomicRows} {C : Set ℕ} (d : ThreeLevelChoice μ C) (ρ : ℕ → PairedMeasure)
    (B Btilde : K → BooleanSubalgebra (Set ℕ))
    (hdir : ∀ i j, ∃ k, B i ≤ B k ∧ Btilde i ≤ Btilde k ∧ B j ≤ B k ∧ Btilde j ≤ Btilde k)
    (h : ∀ k, d.Nonseparated ρ (B k) (Btilde k)) :
    d.Nonseparated ρ (BooleanSubalgebra.closure (⋃ k, (B k : Set (Set ℕ))))
      (BooleanSubalgebra.closure (⋃ k, (Btilde k : Set (Set ℕ)))) :=
  ⟨not_pairedSeparated_directed_limit B Btilde hdir _ _ (fun k => (h k).1),
   not_pairedSeparated_directed_limit B Btilde hdir _ _ (fun k => (h k).2)⟩

theorem goodConstruction_directed_union {I K : Type}
    {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → PairedMeasure) (d : ConstructionData μ μtilde R Rtilde)
    (V : K → Set I) (hdir : Directed (· ⊆ ·) V)
    (hgood : ∀ k, GoodConstruction ρ σ d (V k)) : GoodConstruction ρ σ d (⋃ k, V k) := by
  intro i hi
  obtain ⟨k₀,hk₀⟩ := Set.mem_iUnion.mp hi
  let J := {k : K // i ∈ V k}
  haveI : Nonempty J := ⟨⟨k₀,hk₀⟩⟩
  have hdirJ : Directed (· ⊆ ·) (fun j : J => V j.val) := by
    intro j k
    obtain ⟨l,hjl,hkl⟩ := hdir j.val k.val
    exact ⟨⟨l,hjl j.property⟩, hjl, hkl⟩
  have hcover : (⋃ j : J, V j.val) = ⋃ k, V k := by
    apply Set.Subset.antisymm
    · intro a ha
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨j.val,hj⟩
    · intro a ha
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp ha
      obtain ⟨l,hkl,h₀l⟩ := hdir k k₀
      exact Set.mem_iUnion.mpr ⟨⟨l,h₀l hk₀⟩,hkl hk⟩
  have hremcover : (⋃ j : J, (V j.val \ {i})) = (⋃ k, V k) \ {i} := by
    rw [← hcover]
    ext a
    simp only [Set.mem_iUnion, Set.mem_diff]
    constructor
    · rintro ⟨j,hj,hai⟩
      exact ⟨⟨j,hj⟩,hai⟩
    · rintro ⟨⟨j,hj⟩,hai⟩
      exact ⟨j,hj,hai⟩
  have halg (s : Bool) : constructionAlgebra d s (⋃ k, V k) =
      BooleanSubalgebra.closure (⋃ j : J, (constructionAlgebra d s (V j.val) : Set (Set ℕ))) := by
    rw [← hcover]
    exact stageAlgebra_iUnion _ _
  have hrem (s : Bool) : constructionAlgebra d s ((⋃ k, V k) \ {i}) =
      BooleanSubalgebra.closure (⋃ j : J, (constructionAlgebra d s (V j.val \ {i}) : Set (Set ℕ))) := by
    rw [← hremcover]
    exact stageAlgebra_iUnion _ _
  constructor
  · rw [hrem, halg]
    apply ThreeLevelChoice.Nonseparated.directed_limit
    · intro j k
      obtain ⟨l,hjl,hkl⟩ := hdirJ j k
      exact ⟨l, constructionAlgebra_mono d false (Set.diff_subset_diff_left hjl),
        constructionAlgebra_mono d true hjl,
        constructionAlgebra_mono d false (Set.diff_subset_diff_left hkl),
        constructionAlgebra_mono d true hkl⟩
    · intro j
      exact (hgood j.val i j.property).1
  · rw [halg, hrem]
    apply ThreeLevelChoice.Nonseparated.directed_limit
    · intro j k
      obtain ⟨l,hjl,hkl⟩ := hdirJ j k
      exact ⟨l, constructionAlgebra_mono d false hjl,
        constructionAlgebra_mono d true (Set.diff_subset_diff_left hjl),
        constructionAlgebra_mono d false hkl,
        constructionAlgebra_mono d true (Set.diff_subset_diff_left hkl)⟩
    · intro j
      exact (hgood j.val i j.property).2

end SigmaNonprimarity
