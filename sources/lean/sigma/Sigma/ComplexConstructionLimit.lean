import Sigma.ComplexConstructionState
import Sigma.ComplexLimitSeparation

/-! All four construction invariants persist through directed unions of stages. -/
noncomputable section
open Set ThesisCommon
namespace SigmaNonprimarity

theorem ComplexThreeLevelChoice.PairedNonseparated.directed_limit {K : Type} [Nonempty K]
    {μ : ComplexAtomicRows} {C : Set ℕ} (d : ComplexThreeLevelChoice μ C) (ρ : ℕ → ComplexPairedMeasure)
    (B Btilde : K → BooleanSubalgebra (Set ℕ))
    (hdir : ∀ i j, ∃ k, B i ≤ B k ∧ Btilde i ≤ Btilde k ∧ B j ≤ B k ∧ Btilde j ≤ Btilde k)
    (h : ∀ k, d.PairedNonseparated ρ (B k) (Btilde k)) :
    d.PairedNonseparated ρ (BooleanSubalgebra.closure (⋃ k, (B k : Set (Set ℕ))))
      (BooleanSubalgebra.closure (⋃ k, (Btilde k : Set (Set ℕ)))) :=
  ⟨not_complexPairedSeparated_directed_limit B Btilde hdir _ _ (fun k => (h k).1),
   not_complexPairedSeparated_directed_limit B Btilde hdir _ _ (fun k => (h k).2)⟩

theorem goodComplexConstruction_directed_union {I K : Type}
    {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → ComplexPairedMeasure) (d : ComplexConstructionData μ μtilde R Rtilde)
    (V : K → Set I) (hdir : Directed (· ⊆ ·) V)
    (hgood : ∀ k, GoodComplexConstruction ρ σ d (V k)) : GoodComplexConstruction ρ σ d (⋃ k, V k) := by
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
  have halg (s : Bool) : complexConstructionAlgebra d s (⋃ k, V k) =
      BooleanSubalgebra.closure (⋃ j : J, (complexConstructionAlgebra d s (V j.val) : Set (Set ℕ))) := by
    rw [← hcover]
    exact stageAlgebra_iUnion _ _
  have hrem (s : Bool) : complexConstructionAlgebra d s ((⋃ k, V k) \ {i}) =
      BooleanSubalgebra.closure (⋃ j : J, (complexConstructionAlgebra d s (V j.val \ {i}) : Set (Set ℕ))) := by
    rw [← hremcover]
    exact stageAlgebra_iUnion _ _
  constructor
  · rw [hrem, halg]
    apply ComplexThreeLevelChoice.PairedNonseparated.directed_limit
    · intro j k
      obtain ⟨l,hjl,hkl⟩ := hdirJ j k
      exact ⟨l, complexConstructionAlgebra_mono d false (Set.diff_subset_diff_left hjl),
        complexConstructionAlgebra_mono d true hjl,
        complexConstructionAlgebra_mono d false (Set.diff_subset_diff_left hkl),
        complexConstructionAlgebra_mono d true hkl⟩
    · intro j
      exact (hgood j.val i j.property).1
  · rw [halg, hrem]
    apply ComplexThreeLevelChoice.PairedNonseparated.directed_limit
    · intro j k
      obtain ⟨l,hjl,hkl⟩ := hdirJ j k
      exact ⟨l, complexConstructionAlgebra_mono d false hjl,
        complexConstructionAlgebra_mono d true (Set.diff_subset_diff_left hjl),
        complexConstructionAlgebra_mono d false hkl,
        complexConstructionAlgebra_mono d true (Set.diff_subset_diff_left hkl)⟩
    · intro j
      exact (hgood j.val i j.property).2

end SigmaNonprimarity
