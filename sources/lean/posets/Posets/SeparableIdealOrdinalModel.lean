import ThesisCommon.Analysis.OrdinalOnePointSum
import ThesisCommon.Analysis.CountableCompactShells

/-! Topological assembly tools for the countable compact metric classification. -/
noncomputable section
open Set ThesisCommon Topology
namespace Posets

def HasOrdinalCompactModel (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ α : Ordinal.{0}, Nonempty (X ≃ₜ OrdinalInterval α)

theorem HasOrdinalCompactModel.of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (h : HasOrdinalCompactModel X)
    (e : Y ≃ₜ X) : HasOrdinalCompactModel Y := by
  obtain ⟨α, ⟨f⟩⟩ := h
  exact ⟨α, ⟨e.trans f⟩⟩

theorem hasOrdinalCompactModel_singleton {K : Type*} [TopologicalSpace K] (p : K) :
    HasOrdinalCompactModel ({p} : Set K) := by
  letI : Unique (OrdinalInterval (0 : Ordinal.{0})) :=
    { default := ⟨0, le_rfl, le_rfl⟩
      uniq := fun x => Subtype.ext (le_antisymm x.property.2 x.property.1) }
  exact ⟨0, ⟨Homeomorph.homeomorphOfUnique _ _⟩⟩

theorem HasOrdinalCompactModel.sum {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (hX : HasOrdinalCompactModel X) (hY : HasOrdinalCompactModel Y) :
    HasOrdinalCompactModel (X ⊕ Y) := by
  obtain ⟨α, ⟨e⟩⟩ := hX
  obtain ⟨β, ⟨f⟩⟩ := hY
  exact ⟨α + 1 + β, ⟨(e.sumCongr f).trans (ordinalIntervalSumHomeomorph α β)⟩⟩

def compactClopenPieceSumHomeomorph {K : Type*} [TopologicalSpace K] [T2Space K]
    (A : Set K) (hA : IsCompact A) (U : Set K) (hU : IsClopen U) :
    (↥(A ∩ U) ⊕ ↥(A \ U)) ≃ₜ A := by
  letI : CompactSpace ↥(A ∩ U) := isCompact_iff_compactSpace.mp (hA.inter_right hU.isClosed)
  letI : CompactSpace ↥(A \ U) := isCompact_iff_compactSpace.mp (hA.diff hU.isOpen)
  let f : ↥(A ∩ U) ⊕ ↥(A \ U) → A :=
    Sum.elim (fun x => ⟨x.val, x.property.1⟩) (fun x => ⟨x.val, x.property.1⟩)
  have hc : Continuous f := Continuous.sumElim
    (continuous_subtype_val.subtype_mk _) (continuous_subtype_val.subtype_mk _)
  have hi : Function.Injective f := by
    intro x y h
    have he := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext he)
      | inr y => exact (y.property.2 (he ▸ x.property.2)).elim
    | inr x =>
      cases y with
      | inl y => exact (x.property.2 (he.symm ▸ y.property.2)).elim
      | inr y => exact congrArg Sum.inr (Subtype.ext he)
  have hs : Function.Surjective f := by
    intro x
    by_cases hx : x.val ∈ U
    · exact ⟨Sum.inl ⟨x.val, x.property, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x.val, x.property, hx⟩, rfl⟩
  exact (show Continuous (Equiv.ofBijective f ⟨hi, hs⟩) from hc).homeoOfEquivCompactToT2

theorem hasOrdinalCompactModel_of_clopen_pieces {K : Type*}
    [TopologicalSpace K] [T2Space K] (A : Set K) (hA : IsCompact A)
    (U : Set K) (hU : IsClopen U)
    (hleft : HasOrdinalCompactModel ↥(A ∩ U)) (hright : HasOrdinalCompactModel ↥(A \ U)) :
    HasOrdinalCompactModel A :=
  (hleft.sum hright).of_homeomorph (compactClopenPieceSumHomeomorph A hA U hU).symm

end Posets
