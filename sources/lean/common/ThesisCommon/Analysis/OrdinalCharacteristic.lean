import ThesisCommon.Analysis.OrdinalRank
import ThesisCommon.Analysis.OrdinalFiniteCover

/-! Uniqueness of the characteristic rank of a nonempty compact ordinal set.
The multiplicity is the number of points in its unique finite nonempty
derivative; no homeomorphism classification is postulated. -/
noncomputable section
open Set Order Filter Topology
universe u v
namespace ThesisCommon

theorem derivedSet_eq_empty_of_finite {K : Type v} [TopologicalSpace K] [T1Space K]
    {A : Set K} (hA : A.Finite) : derivedSet A = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  have hc : ClusterPt x (𝓟 (A \ {x})) := accPt_principal_iff_clusterPt.mp hx
  have hm := isClosed_iff_clusterPt.mp (hA.diff.isClosed) x hc
  exact hm.2 (mem_singleton x)

theorem ordinalDerived_succ_eq_empty_of_finite {K : Type v} [TopologicalSpace K] [T1Space K]
    {A : Set K} {α : Ordinal.{u}} (hα : (ordinalDerived A α).Finite) :
    ordinalDerived A (succ α) = ∅ := by
  rw [ordinalDerived_succ]
  exact derivedSet_eq_empty_of_finite hα

theorem ordinalCharacteristic_rank_unique {A : Set Ordinal.{u}} (hA : IsClosed A)
    {α β : Ordinal.{u}} (hα : (ordinalDerived A α).Finite)
    (hneα : (ordinalDerived A α).Nonempty) (hβ : (ordinalDerived A β).Finite)
    (hneβ : (ordinalDerived A β).Nonempty) : α = β := by
  have no_lt {γ δ : Ordinal.{u}} (hfin : (ordinalDerived A γ).Finite)
      (hne : (ordinalDerived A δ).Nonempty) : ¬ γ < δ := by
    intro hlt
    have hsub := ordinalDerived_antitone hA (succ_le_iff.mpr hlt)
    rw [ordinalDerived_succ_eq_empty_of_finite hfin] at hsub
    exact hne.ne_empty (subset_empty_iff.mp hsub)
  exact le_antisymm (not_lt.mp (no_lt hβ hneα)) (not_lt.mp (no_lt hα hneβ))

theorem ordinal_existsUnique_characteristic_rank {A : Set Ordinal.{u}}
    (hA : IsCompact A) (hne : A.Nonempty) :
    ∃! α : Ordinal.{u}, (ordinalDerived A α).Finite ∧ (ordinalDerived A α).Nonempty := by
  obtain ⟨α, hfin, hnonempty, _⟩ := ordinal_exists_finite_nonempty_derivative hA hne
  refine ⟨α, ⟨hfin, hnonempty⟩, ?_⟩
  intro β hβ
  exact ordinalCharacteristic_rank_unique hA.isClosed hβ.1 hβ.2 hfin hnonempty

end ThesisCommon
