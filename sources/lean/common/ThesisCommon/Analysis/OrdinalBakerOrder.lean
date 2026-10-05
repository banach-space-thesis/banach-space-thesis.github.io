import ThesisCommon.Analysis.OrdinalClosedCopies
import Mathlib.Order.UpperLower.Basic

/-! Every nonempty compact ordinal subset is an ordinal interval in its
inherited topology. To enumerate a bounded closed set, append its final
ordinal ray and use the normal enumerator of this unbounded closed set. -/
noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

def ordinalClosedCompletion (A : Set Ordinal.{u}) : Set Ordinal.{u} := A ∪ Ici (sSup A)

theorem ordinalClosedCompletion_unbounded (A : Set Ordinal.{u}) :
    ¬ BddAbove (ordinalClosedCompletion A) := by
  intro h
  exact (not_bddAbove_Ici (a := sSup A))
    (h.mono (subset_union_right : Ici (sSup A) ⊆ A ∪ Ici (sSup A)))

theorem ordinalClosedCompletion_isClosed {A : Set Ordinal.{u}} (hA : IsClosed A) :
    IsClosed (ordinalClosedCompletion A) := hA.union isClosed_Ici

theorem ordinalClosedCompletion_enum_continuous {A : Set Ordinal.{u}} (hA : IsClosed A) :
    Continuous (Ordinal.enumOrd (ordinalClosedCompletion A)) := by
  have hn := (Ordinal.enumOrd_isNormal_iff_isClosed
    (ordinalClosedCompletion_unbounded A)).mpr (ordinalClosedCompletion_isClosed hA)
  exact Order.isNormal_iff_strictMono_and_continuous.mp hn |>.2

/-- The increasing homeomorphic ordinal model of a nonempty compact ordinal
set has an endpoint no greater than the largest point of the original set. -/
theorem ordinal_compact_order_homeomorph {A : Set Ordinal.{u}}
    (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ β : Ordinal.{u}, ∃ e : OrdinalInterval β ≃ₜ A,
      StrictMono (fun x => (e x).val) ∧ β ≤ sSup A := by
  let S := ordinalClosedCompletion A
  have hS : ¬ BddAbove S := ordinalClosedCompletion_unbounded A
  let f := Ordinal.enumOrd S
  have hmono : StrictMono f := Ordinal.enumOrd_strictMono hS
  have hcont : Continuous f := ordinalClosedCompletion_enum_continuous hA.isClosed
  obtain ⟨β, hβ⟩ := Ordinal.enumOrd_surjective hS
    (show sSup A ∈ S from Or.inr (show sSup A ≤ sSup A from le_rfl))
  have hmem (x : OrdinalInterval β) : f x.val ∈ A := by
    have hx : f x.val ≤ sSup A := (hmono.monotone x.property.2).trans_eq hβ
    rcases Ordinal.enumOrd_mem hS x.val with ha | ha
    · exact ha
    · have heq : f x.val = sSup A := le_antisymm hx ha
      rw [heq]
      exact hA.sSup_mem hne
  let g : C(OrdinalInterval β, A) := ⟨fun x => ⟨f x.val, hmem x⟩,
    (hcont.comp continuous_subtype_val).subtype_mk _⟩
  have hgmono : StrictMono g := fun x y hxy => hmono hxy
  have hgsurj : Function.Surjective g := by
    intro a
    obtain ⟨γ, hγ⟩ := Ordinal.enumOrd_surjective hS (show a.val ∈ S from Or.inl a.property)
    have hγβ : γ ≤ β := hmono.le_iff_le.mp (by
      rw [show f γ = a.val from hγ, show f β = sSup A from hβ]
      exact le_csSup hA.bddAbove a.property)
    refine ⟨⟨γ, bot_le, hγβ⟩, ?_⟩
    exact Subtype.ext hγ
  let e := (show Continuous (Equiv.ofBijective g ⟨hgmono.injective, hgsurj⟩) from
    g.continuous).homeoOfEquivCompactToT2
  refine ⟨β, e, ?_, ?_⟩
  · exact fun x y hxy => hmono hxy
  · exact (Ordinal.le_enumOrd_self hS).trans_eq hβ

end ThesisCommon
