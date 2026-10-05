import Sigma.ComplexSplitSelection
import Sigma.LimitSeparation
import ThesisCommon.Analysis.BooleanClosure
import ThesisCommon.Analysis.DirectedSeparation

/-! Nonseparation at a directed limit: every finite witness already occurs at
one stage. No countable-cofinality or regularity hypothesis is used. -/
noncomputable section
open Set ThesisCommon
namespace SigmaNonprimarity

theorem complexFinitelySeparated_directed_union_iff {D T I : Type*} [Nonempty I]
    (ev : D → T → ℂ) (S : I → Set T) (hdir : Directed (· ⊆ ·) S) (M N : Set D) :
    ComplexFinitelySeparated ev (⋃ i, S i) M N ↔
      ∃ i, ComplexFinitelySeparated ev (S i) M N := by
  constructor
  · rintro ⟨ε,hε,F,hF,hgap⟩
    obtain ⟨i,hi⟩ := finite_subset_directed_union S hdir F hF
    exact ⟨i,ε,hε,F,hi,hgap⟩
  · rintro ⟨i,ε,hε,F,hF,hgap⟩
    exact ⟨ε,hε,F,hF.trans (Set.subset_iUnion S i),hgap⟩

theorem complexPairedSeparated_raw_iff (B Btilde : BooleanSubalgebra (Set ℕ))
    (M N : Set ComplexPairedMeasure) :
    ComplexPairedSeparated B Btilde M N ↔
      ComplexFinitelySeparated (fun μ t => μ (rawPairedTest t)) (allowedPairedTests B Btilde) M N := by
  classical
  constructor
  · rintro ⟨ε, hε, F, _, hgap⟩
    let forget : B ⊕ Btilde → Set ℕ ⊕ Set ℕ := Sum.map Subtype.val Subtype.val
    refine ⟨ε, hε, F.image forget, ?_, ?_⟩
    · intro t ht
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
      cases u with
      | inl A => exact A.property
      | inr A => exact A.property
    · intro μ hμ ν hν
      obtain ⟨t, ht, h⟩ := hgap μ hμ ν hν
      refine ⟨forget t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
      cases t <;> exact h
  · rintro ⟨ε, hε, F, hF, hgap⟩
    let inclusion : F → B ⊕ Btilde := fun t =>
      match h : t.val with
      | .inl A => .inl ⟨A, by simpa [allowedPairedTests, h] using hF t.property⟩
      | .inr A => .inr ⟨A, by simpa [allowedPairedTests, h] using hF t.property⟩
    have heval (t : F) : pairedTest B Btilde (inclusion t) = rawPairedTest t.val := by
      simp only [inclusion]
      split <;> rename_i A h <;> simp only [h, pairedTest, rawPairedTest]
    refine ⟨ε, hε, Finset.univ.image inclusion, Set.subset_univ _, ?_⟩
    intro μ hμ ν hν
    obtain ⟨t, ht, h⟩ := hgap μ hμ ν hν
    refine ⟨inclusion ⟨t, ht⟩, Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa only [heval] using h

theorem complexPairedSeparated_directed_limit_iff {I : Type*} [Nonempty I]
    (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (hdir : ∀ i j, ∃ k, B i ≤ B k ∧ Btilde i ≤ Btilde k ∧ B j ≤ B k ∧ Btilde j ≤ Btilde k)
    (M N : Set ComplexPairedMeasure) :
    ComplexPairedSeparated (BooleanSubalgebra.closure (⋃ i, (B i : Set (Set ℕ))))
      (BooleanSubalgebra.closure (⋃ i, (Btilde i : Set (Set ℕ)))) M N ↔
      ∃ i, ComplexPairedSeparated (B i) (Btilde i) M N := by
  have hB : Directed (· ≤ ·) B := fun i j => by
    obtain ⟨k, hi, _, hj, _⟩ := hdir i j
    exact ⟨k, hi, hj⟩
  have hBt : Directed (· ≤ ·) Btilde := fun i j => by
    obtain ⟨k, _, hi, _, hj⟩ := hdir i j
    exact ⟨k, hi, hj⟩
  have htests : allowedPairedTests
      (BooleanSubalgebra.closure (⋃ i, (B i : Set (Set ℕ))))
      (BooleanSubalgebra.closure (⋃ i, (Btilde i : Set (Set ℕ)))) =
      ⋃ i, allowedPairedTests (B i) (Btilde i) := by
    ext t
    cases t with
    | inl A =>
      change A ∈ BooleanSubalgebra.closure (⋃ i, (B i : Set (Set ℕ))) ↔ _
      constructor
      · intro h
        obtain ⟨i, hi⟩ := booleanClosure_directed_union_mem B hB h
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      · intro h
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
        exact BooleanSubalgebra.subset_closure (Set.mem_iUnion.mpr ⟨i, hi⟩)
    | inr A =>
      change A ∈ BooleanSubalgebra.closure (⋃ i, (Btilde i : Set (Set ℕ))) ↔ _
      constructor
      · intro h
        obtain ⟨i, hi⟩ := booleanClosure_directed_union_mem Btilde hBt h
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      · intro h
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
        exact BooleanSubalgebra.subset_closure (Set.mem_iUnion.mpr ⟨i, hi⟩)
  have htestdir : Directed (· ⊆ ·) (fun i => allowedPairedTests (B i) (Btilde i)) := by
    intro i j
    obtain ⟨k, hi, hit, hj, hjt⟩ := hdir i j
    refine ⟨k, ?_, ?_⟩
    · intro t ht
      cases t with | inl A => exact hi ht | inr A => exact hit ht
    · intro t ht
      cases t with | inl A => exact hj ht | inr A => exact hjt ht
  simp_rw [complexPairedSeparated_raw_iff]
  rw [htests, complexFinitelySeparated_directed_union_iff _ _ htestdir]

theorem not_complexPairedSeparated_directed_limit {I : Type*} [Nonempty I]
    (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (hdir : ∀ i j, ∃ k, B i ≤ B k ∧ Btilde i ≤ Btilde k ∧ B j ≤ B k ∧ Btilde j ≤ Btilde k)
    (M N : Set ComplexPairedMeasure) (hn : ∀ i, ¬ ComplexPairedSeparated (B i) (Btilde i) M N) :
    ¬ ComplexPairedSeparated (BooleanSubalgebra.closure (⋃ i, (B i : Set (Set ℕ))))
      (BooleanSubalgebra.closure (⋃ i, (Btilde i : Set (Set ℕ)))) M N := by
  intro h
  obtain ⟨i, hi⟩ := (complexPairedSeparated_directed_limit_iff B Btilde hdir M N).mp h
  exact hn i hi

end SigmaNonprimarity
