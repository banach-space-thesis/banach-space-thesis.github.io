import ThesisCommon.Analysis.ContinuousMapPullback
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Analysis.Real.Cardinality

/-! The actual Cantor embeddings used in Milutin's theorem. Compact metric
spaces are Polish, so their uncountability supplies a continuous injection
of the binary Cantor space. -/

noncomputable section
open Set
namespace ThesisCommon

theorem milutin_exists_cantor_embedding (K : Type*)
    [MetricSpace K] [CompactSpace K] [Uncountable K] :
    ∃ e : C((ℕ → Bool), K), Function.Injective e := by
  obtain ⟨f, _, hf, hinj⟩ :=
    isClosed_univ.exists_nat_bool_injection_of_not_countable
      (α := K) Set.not_countable_univ
  exact ⟨⟨f, hf⟩, hinj⟩

theorem milutin_exists_interval_cantor_embedding :
    ∃ e : C((ℕ → Bool), UnitInterval), Function.Injective e := by
  have hunc : ¬(Set.Icc (0 : ℝ) 1).Countable := by
    rw [Cardinal.Real.Icc_countable_iff]
    norm_num
  obtain ⟨f, hfI, hf, hinj⟩ :=
    isClosed_Icc.exists_nat_bool_injection_of_not_countable hunc
  refine ⟨⟨fun x => ⟨f x, hfI ⟨x, rfl⟩⟩, hf.subtype_mk _⟩, ?_⟩
  intro x y hxy
  exact hinj (congrArg Subtype.val hxy)

end ThesisCommon
