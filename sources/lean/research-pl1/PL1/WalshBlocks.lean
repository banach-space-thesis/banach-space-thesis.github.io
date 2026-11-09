import PL1.WalshExpectations
import PL1.LpInclusions
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Exact dimensions of the finite-coordinate Walsh spaces -/

noncomputable section
open MeasureTheory
open scoped ENNReal Topology BigOperators

namespace PL1.WalshBlocks

open Walsh WalshExpectations

variable (K : Type*) [RCLike K]

theorem l2ToL1_injective : Function.Injective (l2ToL1 (𝕜 := K)) := by
  intro f g h
  apply Lp.ext
  filter_upwards [ProbabilityLp.coeFn_inclusion haar 1 2 (by norm_num) f,
    ProbabilityLp.coeFn_inclusion haar 1 2 (by norm_num) g] with x hf hg
  change l2ToL1 f x = f x at hf
  change l2ToL1 g x = g x at hg
  rw [← hf, ← hg, h]

/-- Walsh characters remain linearly independent in actual L1. -/
theorem linearIndependent_characterL1 : LinearIndependent K (scalarCharacterLp K 1) := by
  have h := (orthonormal_scalarCharacterL2 K).linearIndependent.map'
    (l2ToL1 (𝕜 := K)).toLinearMap (LinearMap.ker_eq_bot.mpr (l2ToL1_injective K))
  simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, l2ToL1_scalarCharacter] using h

theorem range_expectationL1_eq (m : ℕ) :
    (expectationL1 K m).range = finiteSpan K m := by
  apply le_antisymm (range_expectationL1_le K m)
  apply Submodule.span_le.mpr
  rintro x ⟨F, hF, rfl⟩
  refine ⟨scalarCharacterLp K 1 F, ?_⟩
  change expectationL1 K m (scalarCharacterLp K 1 F) = scalarCharacterLp K 1 F
  simp only [expectationL1_character, Finset.mem_powerset.mp hF, ite_true]

theorem finiteSpan_eq_span_range (m : ℕ) :
    finiteSpan K m = Submodule.span K
      (Set.range (fun F : (Finset.range m).powerset => scalarCharacterLp K 1 F)) := by
  unfold finiteSpan
  congr 1
  ext x
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨⟨F, hF⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    exact ⟨F, F.property, rfl⟩

theorem finrank_finiteSpan (m : ℕ) : Module.finrank K (finiteSpan K m) = 2 ^ m := by
  rw [finiteSpan_eq_span_range]
  have h := (linearIndependent_characterL1 K).comp
    (fun F : (Finset.range m).powerset => (F : Finset ℕ)) Subtype.val_injective
  simp only [Function.comp_def] at h
  rw [finrank_span_eq_card h]
  simp

/-- The genuine m-coordinate expectation has rank exactly 2^m. -/
theorem finrank_range_expectationL1 (m : ℕ) :
    Module.finrank K (expectationL1 K m).range = 2 ^ m := by
  rw [range_expectationL1_eq, finrank_finiteSpan]

/-- The next-coordinate Walsh block. -/
def blockL1 (m : ℕ) : Lp K 1 haar →L[K] Lp K 1 haar :=
  expectationL1 K (m + 1) - expectationL1 K m

theorem blockL1_character (m : ℕ) (F : Finset ℕ) :
    blockL1 K m (scalarCharacterLp K 1 F) =
      if m ∈ F ∧ F ⊆ Finset.range (m + 1) then scalarCharacterLp K 1 F else 0 := by
  simp only [blockL1, sub_apply, expectationL1_character]
  by_cases hs : F ⊆ Finset.range (m + 1)
  · by_cases hm : m ∈ F
    · have hn : ¬ F ⊆ Finset.range m := by
        intro h
        exact (Nat.lt_irrefl m) (Finset.mem_range.mp (h hm))
      simp [hs, hm, hn]
    · have hn : F ⊆ Finset.range m := by
        intro j hj
        have hjm := Finset.mem_range.mp (hs hj)
        have hjne : j ≠ m := by intro h; exact hm (h ▸ hj)
        exact Finset.mem_range.mpr (by omega)
      simp [hs, hm, hn]
  · have hn : ¬ F ⊆ Finset.range m :=
      fun h => hs (h.trans (Finset.range_mono (Nat.le_succ m)))
    simp [hs, hn]

def blockFamily (m : ℕ) (F : (Finset.range m).powerset) : Lp K 1 haar :=
  scalarCharacterLp K 1 (insert m F)

def blockSpan (m : ℕ) : Submodule K (Lp K 1 haar) :=
  Submodule.span K (Set.range (blockFamily K m))

theorem not_mem_support (m : ℕ) (F : (Finset.range m).powerset) : m ∉ (F : Finset ℕ) := by
  intro h
  exact (Nat.lt_irrefl m) (Finset.mem_range.mp (Finset.mem_powerset.mp F.property h))

theorem blockSupport_injective (m : ℕ) :
    Function.Injective (fun F : (Finset.range m).powerset => insert m (F : Finset ℕ)) := by
  intro F H h
  apply Subtype.ext
  have he := congrArg (fun S : Finset ℕ => S.erase m) h
  simpa [not_mem_support m F, not_mem_support m H] using he

theorem linearIndependent_blockFamily (m : ℕ) : LinearIndependent K (blockFamily K m) :=
  (linearIndependent_characterL1 K).comp _ (blockSupport_injective m)

instance (m : ℕ) : FiniteDimensional K (blockSpan K m) :=
  FiniteDimensional.span_of_finite K (Set.finite_range (blockFamily K m))

theorem finrank_blockSpan (m : ℕ) : Module.finrank K (blockSpan K m) = 2 ^ m := by
  rw [blockSpan, finrank_span_eq_card (linearIndependent_blockFamily K m)]
  simp

theorem character_mem_blockSpan (m : ℕ) (F : Finset ℕ)
    (hm : m ∈ F) (hF : F ⊆ Finset.range (m + 1)) :
    scalarCharacterLp K 1 F ∈ blockSpan K m := by
  apply Submodule.subset_span
  have he : F.erase m ⊆ Finset.range m := by
    intro j hj
    have hjF := Finset.mem_of_mem_erase hj
    have hjne := Finset.ne_of_mem_erase hj
    have hjm := Finset.mem_range.mp (hF hjF)
    exact Finset.mem_range.mpr (by omega)
  refine ⟨⟨F.erase m, Finset.mem_powerset.mpr he⟩, ?_⟩
  change scalarCharacterLp K 1 (insert m (F.erase m)) = _
  rw [Finset.insert_erase hm]

theorem blockL1_mem_blockSpan (m : ℕ) (f : Lp K 1 haar) :
    blockL1 K m f ∈ blockSpan K m := by
  let S := (blockSpan K m).comap (blockL1 K m).toLinearMap
  have hc : IsClosed (S : Set (Lp K 1 haar)) :=
    (blockSpan K m).closed_of_finiteDimensional.preimage (blockL1 K m).continuous
  have hs : Submodule.span K (Set.range (scalarCharacterLp K 1)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨F, rfl⟩
    change blockL1 K m (scalarCharacterLp K 1 F) ∈ blockSpan K m
    rw [blockL1_character]
    split_ifs with h
    · exact character_mem_blockSpan K m F h.1 h.2
    · exact Submodule.zero_mem _
  exact hc.closure_subset_iff.mpr hs (dense_span_scalarCharacterLp K 1 (by norm_num) f)

theorem blockL1_blockFamily (m : ℕ) (F : (Finset.range m).powerset) :
    blockL1 K m (blockFamily K m F) = blockFamily K m F := by
  rw [blockFamily, blockL1_character]
  have hs : insert m (F : Finset ℕ) ⊆ Finset.range (m + 1) := by
    apply Finset.insert_subset_iff.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_self m),
      (Finset.mem_powerset.mp F.property).trans (Finset.range_mono (Nat.le_succ m))⟩
  simp only [Finset.mem_insert_self, hs, and_self, ite_true]

theorem range_blockL1_eq (m : ℕ) : (blockL1 K m).range = blockSpan K m := by
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    exact blockL1_mem_blockSpan K m f
  · apply Submodule.span_le.mpr
    rintro x ⟨F, rfl⟩
    exact ⟨blockFamily K m F, blockL1_blockFamily K m F⟩

theorem finrank_range_blockL1 (m : ℕ) : Module.finrank K (blockL1 K m).range = 2 ^ m := by
  rw [range_blockL1_eq, finrank_blockSpan]

end PL1.WalshBlocks
