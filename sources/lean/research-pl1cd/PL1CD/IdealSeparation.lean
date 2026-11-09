import PL1CD.DunfordPettisIdeals
import PL1CD.Cardinality
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

noncomputable section
open scoped Topology

namespace PL1CD

variable (𝕜 : Type) [RCLike 𝕜]

structure IdealSeparationData (P : ContinuumIndex → L1Operator 𝕜) where
  test : ContinuumIndex → L1Operator 𝕜
  seminorm : ContinuumIndex → Seminorm 𝕜 (L1Operator 𝕜)
  continuous : ∀ a, Continuous (seminorm a)
  bound : ∀ a T, seminorm a T ≤ 2 * ‖T‖
  test_norm : ∀ a, ‖test a‖ = 1
  test_value : ∀ a, seminorm a (test a) = 2
  test_factors : ∀ a, test a ∈ generatedIdeal 𝕜 P {a}
  off_diagonal : ∀ a b, a ≠ b → ∀ U V : L1Operator 𝕜,
    seminorm a (V.comp ((P b).comp U)) = 0

namespace IdealSeparationData

variable {𝕜}
variable {P : ContinuumIndex → L1Operator 𝕜} (d : IdealSeparationData 𝕜 P)
include d

theorem seminorm_zero_on_generated {a : ContinuumIndex} {S : Set ContinuumIndex}
    (ha : a ∉ S) {T : L1Operator 𝕜} (hT : T ∈ generatedIdeal 𝕜 P S) :
    d.seminorm a T = 0 := by
  change T ∈ closure (algebraicGeneratedIdeal 𝕜 P S : Set (L1Operator 𝕜)) at hT
  apply closure_minimal (s := (algebraicGeneratedIdeal 𝕜 P S : Set (L1Operator 𝕜)))
    (t := {T | d.seminorm a T = 0}) ?_
    (isClosed_eq (d.continuous a) continuous_const) hT
  intro W hW
  obtain ⟨ts, hts, rfl⟩ := hW
  induction ts with
  | nil => simp
  | cons t ts ih =>
      rw [List.map_cons, List.sum_cons]
      have hneq : a ≠ t.1 := by
        intro h
        exact ha (h ▸ hts t (by simp))
      have hhead := d.off_diagonal a t.1 hneq t.2.1 t.2.2
      have htail := ih (fun u hu => hts u (by simp [hu]))
      change d.seminorm a (sandwichValue 𝕜 P t) = 0 at hhead
      change d.seminorm a (List.map (sandwichValue 𝕜 P) ts).sum = 0 at htail
      apply le_antisymm _ (apply_nonneg _ _)
      calc
        _ ≤ d.seminorm a (sandwichValue 𝕜 P t) +
            d.seminorm a (List.map (sandwichValue 𝕜 P) ts).sum := map_add_le_add _ _ _
        _ = 0 := by rw [hhead, htail]; simp

theorem norm_gap {a : ContinuumIndex} {S : Set ContinuumIndex}
    (ha : a ∉ S) {T : L1Operator 𝕜} (hT : T ∈ generatedIdeal 𝕜 P S) :
    1 ≤ ‖d.test a - T‖ := by
  have hzero := d.seminorm_zero_on_generated ha hT
  have hadd := map_add_le_add (d.seminorm a) (d.test a - T) T
  rw [sub_add_cancel, d.test_value, hzero, add_zero] at hadd
  have hbound := d.bound a (d.test a - T)
  linarith

theorem test_mem_iff (a : ContinuumIndex) (S : Set ContinuumIndex) :
    d.test a ∈ generatedIdeal 𝕜 P S ↔ a ∈ S := by
  constructor
  · intro h
    by_contra ha
    have hgap := d.norm_gap ha h
    norm_num at hgap
  · intro ha
    exact generatedIdeal_mono 𝕜 P (Set.singleton_subset_iff.mpr ha) (d.test_factors a)

theorem generatedIdeal_le_iff (S T : Set ContinuumIndex) :
    generatedIdeal 𝕜 P S ≤ generatedIdeal 𝕜 P T ↔ S ⊆ T := by
  constructor
  · intro h a ha
    exact (d.test_mem_iff a T).mp (h ((d.test_mem_iff a S).mpr ha))
  · exact generatedIdeal_mono 𝕜 P

theorem generatedIdeal_injective : Function.Injective (generatedIdeal 𝕜 P) := by
  intro S T h
  exact Set.Subset.antisymm ((d.generatedIdeal_le_iff S T).mp h.le)
    ((d.generatedIdeal_le_iff T S).mp h.ge)

theorem orderSpec (hschur : ∀ a, PL1.HasSchurProperty 𝕜 (P a).range) :
    TheoremDOrderSpec 𝕜 (generatedIdeal 𝕜 P) :=
  ⟨fun S => ⟨generatedIdeal_isClosedTwoSided 𝕜 P S,
    generatedIdeal_isProper 𝕜 P hschur S⟩, d.generatedIdeal_le_iff⟩

def closedIdealFamily (_d : IdealSeparationData 𝕜 P)
    (S : Set ContinuumIndex) : ClosedOperatorIdeals 𝕜 :=
  ⟨generatedIdeal 𝕜 P S, generatedIdeal_isClosedTwoSided 𝕜 P S⟩

theorem closedIdealFamily_injective : Function.Injective (d.closedIdealFamily) := by
  intro S T h
  apply d.generatedIdeal_injective
  exact congrArg Subtype.val h

theorem cardinality : ClosedIdealCardinalityStatement 𝕜 := by
  apply le_antisymm (closedOperatorIdeals_cardinality_le 𝕜)
  have h := Cardinal.mk_le_of_injective d.closedIdealFamily_injective
  simpa [Cardinal.mk_set, ContinuumIndex] using h

theorem theoremD (hschur : ∀ a, PL1.HasSchurProperty 𝕜 (P a).range) :
    TheoremDStatement 𝕜 :=
  ⟨⟨generatedIdeal 𝕜 P, d.orderSpec hschur⟩, d.cardinality⟩

end IdealSeparationData
end PL1CD
