import ThesisCommon.Analysis.OrdinalBakerOrder
import ThesisCommon.Analysis.OrdinalIntervalSum
import Mathlib.Topology.Constructions.SumProd

/-! Finite ordinal models and the clopen two-piece gluing operation needed
by the countable compact metric classification induction. -/
noncomputable section
open Set Topology
universe u
namespace ThesisCommon

theorem finiteCompact_exists_ordinal_model (K : Type u)
    [TopologicalSpace K] [CompactSpace K] [T2Space K] [Finite K] [Nonempty K] :
    ∃ α : Ordinal.{u}, Nonempty (K ≃ₜ OrdinalInterval α) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let f : K → Ordinal.{u} := fun x => ((Fintype.equivFin K x).val : Ordinal.{u})
  have hf : Function.Injective f := by
    intro x y h
    apply (Fintype.equivFin K).injective
    apply Fin.ext
    dsimp only [f] at h
    exact_mod_cast h
  have hc : Continuous f := continuous_of_discreteTopology
  let e : K ≃ₜ range f :=
    (show Continuous (Equiv.ofInjective f hf) from hc.subtype_mk _).homeoOfEquivCompactToT2
  have hr : IsCompact (range f) := by simpa only [image_univ] using isCompact_univ.image hc
  have hn : (range f).Nonempty := Set.range_nonempty f
  obtain ⟨α, h, _, _⟩ := ordinal_compact_order_homeomorph hr hn
  exact ⟨α, ⟨e.trans h.symm⟩⟩

def compactClopenSumHomeomorph {K : Type u} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (U : Set K) (hU : IsClopen U) :
    (↥U ⊕ ↥(Uᶜ)) ≃ₜ K := by
  classical
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isClosed.isCompact
  letI : CompactSpace ↥(Uᶜ) := isCompact_iff_compactSpace.mp hU.compl.isClosed.isCompact
  let f : ↥U ⊕ ↥(Uᶜ) → K := Sum.elim Subtype.val Subtype.val
  have hc : Continuous f := Continuous.sumElim continuous_subtype_val continuous_subtype_val
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext hxy)
        | inr y =>
          change x.val = y.val at hxy
          exact False.elim (y.property (hxy ▸ x.property))
      | inr x =>
        cases y with
        | inl y =>
          change x.val = y.val at hxy
          exact False.elim (x.property (hxy.symm ▸ y.property))
        | inr y => exact congrArg Sum.inr (Subtype.ext hxy)
    · intro x
      by_cases hx : x ∈ U
      · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
      · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  exact (show Continuous (Equiv.ofBijective f hf) from hc).homeoOfEquivCompactToT2

theorem compactClopen_glue_ordinal_models {K : Type u} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (U : Set K) (hU : IsClopen U)
    {α β : Ordinal.{u}} (eU : U ≃ₜ OrdinalInterval α)
    (eV : ↥(Uᶜ) ≃ₜ OrdinalInterval β) :
    Nonempty (K ≃ₜ OrdinalInterval (α + 1 + β)) :=
  ⟨(compactClopenSumHomeomorph U hU).symm.trans
    ((eU.sumCongr eV).trans (ordinalIntervalSumHomeomorph α β))⟩

end ThesisCommon
