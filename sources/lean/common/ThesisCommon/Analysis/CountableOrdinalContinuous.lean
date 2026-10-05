import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Actual countable ordinal intervals and separability of their continuous
function spaces. The ordinal and scalar universes are independent. -/
noncomputable section
open Set TopologicalSpace
namespace ThesisCommon
universe u

theorem ordinalInterval_countable {α : Ordinal.{u}}
    (hα : α < (Cardinal.aleph 1).ord) : Countable (OrdinalInterval α) := by
  have hcard : α.card < Cardinal.aleph 1 := Cardinal.lt_ord.mp hα
  have hIio : (Set.Iio α).Countable := by
    apply (Cardinal.countable_iff_lt_aleph_one _).mpr
    rw [Ordinal.mk_Iio_ordinal, ← not_le, Cardinal.aleph1_le_lift, not_le]
    exact hcard
  have hIcc : (Set.Icc 0 α).Countable :=
    (hIio.union (Set.countable_singleton α)).mono (by
      intro β hβ
      rcases lt_or_eq_of_le hβ.2 with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq)
  exact hIcc.to_subtype

theorem countable_orderTopology_secondCountable (A : Type*) [Preorder A]
    [TopologicalSpace A] [OrderTopology A] [Countable A] : SecondCountableTopology A := by
  refine ⟨⟨{s | ∃ a : A, s = Ioi a ∨ s = Iio a}, ?_,
    OrderTopology.topology_eq_generate_intervals⟩⟩
  have heq : {s | ∃ a : A, s = Ioi a ∨ s = Iio a} =
      Set.range (Ioi : A → Set A) ∪ Set.range (Iio : A → Set A) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_range]
    aesop
  rw [heq]
  exact (Set.countable_range _).union (Set.countable_range _)

theorem ordinalContinuous_separable (𝕜 : Type*) [RCLike 𝕜] {α : Ordinal.{u}}
    (hα : α < (Cardinal.aleph 1).ord) : SeparableSpace (OrdinalContinuous 𝕜 α) := by
  letI := ordinalInterval_countable hα
  letI := countable_orderTopology_secondCountable (OrdinalInterval α)
  infer_instance

end ThesisCommon
