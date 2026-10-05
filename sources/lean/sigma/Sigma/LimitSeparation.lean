import Sigma.SplitSelection
import ThesisCommon.Analysis.BooleanClosure
import ThesisCommon.Analysis.DirectedSeparation

/-! Nonseparation at a directed limit: every finite witness already occurs at
one stage. No countable-cofinality or regularity hypothesis is used. -/
noncomputable section
open Set ThesisCommon
namespace SigmaNonprimarity

def rawPairedTest : Set ℕ ⊕ Set ℕ → Set (ℕ ⊕ ℕ)
  | .inl A => Sum.inl '' A
  | .inr A => Sum.inr '' A

def allowedPairedTests (B Btilde : BooleanSubalgebra (Set ℕ)) : Set (Set ℕ ⊕ Set ℕ) :=
  {t | match t with | .inl A => A ∈ B | .inr A => A ∈ Btilde}

theorem pairedSeparated_raw_iff (B Btilde : BooleanSubalgebra (Set ℕ))
    (M N : Set PairedMeasure) :
    PairedSeparated B Btilde M N ↔
      FinitelySeparated (fun μ t => μ (rawPairedTest t)) (allowedPairedTests B Btilde) M N := by
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

theorem pairedSeparated_directed_limit_iff {I : Type*} [Nonempty I]
    (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (hdir : ∀ i j, ∃ k, B i ≤ B k ∧ Btilde i ≤ Btilde k ∧ B j ≤ B k ∧ Btilde j ≤ Btilde k)
    (M N : Set PairedMeasure) :
    PairedSeparated (BooleanSubalgebra.closure (⋃ i, (B i : Set (Set ℕ))))
      (BooleanSubalgebra.closure (⋃ i, (Btilde i : Set (Set ℕ)))) M N ↔
      ∃ i, PairedSeparated (B i) (Btilde i) M N := by
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
  simp_rw [pairedSeparated_raw_iff]
  rw [htests, finitelySeparated_directed_union_iff _ _ htestdir]

theorem not_pairedSeparated_directed_limit {I : Type*} [Nonempty I]
    (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (hdir : ∀ i j, ∃ k, B i ≤ B k ∧ Btilde i ≤ Btilde k ∧ B j ≤ B k ∧ Btilde j ≤ Btilde k)
    (M N : Set PairedMeasure) (hn : ∀ i, ¬ PairedSeparated (B i) (Btilde i) M N) :
    ¬ PairedSeparated (BooleanSubalgebra.closure (⋃ i, (B i : Set (Set ℕ))))
      (BooleanSubalgebra.closure (⋃ i, (Btilde i : Set (Set ℕ)))) M N := by
  intro h
  obtain ⟨i, hi⟩ := (pairedSeparated_directed_limit_iff B Btilde hdir M N).mp h
  exact hn i hi

end SigmaNonprimarity
