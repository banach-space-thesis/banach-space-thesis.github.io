import Posets.BorelMatchingCore
import Posets.BorelMatchingScheme
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! An analytic relation either has a countable vertex cover or has a Cantor
family of pairwise vertex-disjoint edges. Edges may be loops. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
namespace Posets

theorem analytic_square_matching_dichotomy {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]
    {R : Set (Y × Y)} (hR : AnalyticSet R) :
    (∃ A : Set Y, A.Countable ∧ ∀ e ∈ R, e.1 ∈ A ∨ e.2 ∈ A) ∨
    (∃ f : (ℕ → Bool) → Y × Y, Set.range f ⊆ R ∧
      Pairwise fun x y => Disjoint ({(f x).1, (f x).2} : Set Y) {(f y).1, (f y).2}) := by
  classical
  rw [AnalyticSet] at hR
  rcases hR with hR | ⟨g, hg, hr⟩
  · left
    exact ⟨∅, Set.countable_empty, by simp [hR]⟩
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable Y
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable (ℕ → ℕ)
  let p : (ℕ → ℕ) → Y := fun z => (g z).1
  let q : (ℕ → ℕ) → Y := fun z => (g z).2
  by_cases hsmall : CountablyCoordinateCovered p q univ
  · obtain ⟨A, hAc, hA⟩ := hsmall
    left
    refine ⟨A, hAc, ?_⟩
    intro e he
    obtain ⟨z, rfl⟩ : e ∈ Set.range g := by rwa [hr]
    exact hA z trivial
  · obtain ⟨C, hC, hCn, hClarge⟩ := exists_closed_core_of_not_small
      (CountablyCoordinateCovered p q)
      (fun {s t} hst ht => countablyCoordinateCovered_mono hst ht)
      (fun S hS hs => countablyCoordinateCovered_sUnion p q S hS hs) hsmall
    letI : CompleteSpace C := hC.isComplete.completeSpace_coe
    letI : Nonempty C := by
      obtain ⟨x, hx⟩ := hCn
      exact ⟨⟨x, hx⟩⟩
    have hlarge : ∀ U : Set C, IsOpen U → U.Nonempty →
        ¬ CountablyCoordinateCovered (p ∘ Subtype.val) (q ∘ Subtype.val) U := by
      intro U hU hn hs
      obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
      have hmeet : (C ∩ V).Nonempty := by
        obtain ⟨x, hx⟩ := hn
        exact ⟨x.val, x.property, hx⟩
      apply hClarge V hV hmeet
      rw [← Subtype.image_preimage_val C V]
      exact (countablyCoordinateCovered_image_iff p q Subtype.val _).mpr hs
    obtain ⟨f, _, hf⟩ := exists_cantor_coordinate_matching
      (p ∘ Subtype.val) (q ∘ Subtype.val)
      (hg.fst.comp continuous_subtype_val) (hg.snd.comp continuous_subtype_val) hlarge
    right
    refine ⟨fun x => g (f x).val, ?_, hf⟩
    rintro e ⟨x, rfl⟩
    rw [← hr]
    exact ⟨(f x).val, rfl⟩

/-- The Borel square matching dichotomy used in Lemma 5.2, with Cantor indexing
and no requirement that the two coordinates of a single edge differ. -/
theorem borel_square_matching_dichotomy
    {R : Set ((ℕ → Bool) × (ℕ → Bool))}
    (hR : @MeasurableSet _ (borel _) R) :
    (∃ A : Set (ℕ → Bool), A.Countable ∧ ∀ e ∈ R, e.1 ∈ A ∨ e.2 ∈ A) ∨
    (∃ f : (ℕ → Bool) → (ℕ → Bool) × (ℕ → Bool), Set.range f ⊆ R ∧
      Pairwise fun x y => Disjoint
        ({(f x).1, (f x).2} : Set (ℕ → Bool)) {(f y).1, (f y).2}) := by
  letI : PolishSpace (ℕ → Bool) := by constructor
  letI : PolishSpace ((ℕ → Bool) × (ℕ → Bool)) := by constructor
  letI : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool)) := borel _
  letI : BorelSpace ((ℕ → Bool) × (ℕ → Bool)) := ⟨rfl⟩
  exact analytic_square_matching_dichotomy hR.analyticSet

end Posets
