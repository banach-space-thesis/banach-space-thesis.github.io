import Posets.CountableOrdinalNormalization
import Posets.PrimaryFactorizationTransport
import Posets.SeparableIdealCorollary

/-! Passing the canonical countable-ordinal factorisation theorem to the
paper's ordinal and compact-metric ideal assertions. -/
noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem countableOrdinal_hasPFP_of_canonical
    (hcanonical : ∀ η : Ordinal.{0}, η.card ≤ Cardinal.aleph0 →
      HasPFP 𝕜 (OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ η))))
    (α : Ordinal.{0}) (hcα : α.card ≤ Cardinal.aleph0) (hα : Ordinal.omega0 ≤ α) :
    HasPFP 𝕜 (OrdinalSpace 𝕜 α) := by
  obtain ⟨η, hcη, ⟨e⟩⟩ := exists_countableOrdinal_normal_form (𝕜 := 𝕜) α hcα hα
  exact hasPFP_of_equiv (hcanonical η hcη) e.symm

theorem ordinal_card_le_aleph0_of_countable_interval (α : Ordinal.{0})
    [Countable (OrdinalInterval α)] : α.card ≤ Cardinal.aleph0 := by
  letI : Countable (Iio α) := Function.Injective.countable
    (f := fun x : Iio α => (⟨x.val, Ordinal.zero_le _, x.property.le⟩ : OrdinalInterval α))
    (fun x y h => Subtype.ext (congrArg (fun z : OrdinalInterval α => z.val) h))
  have h : Cardinal.mk (Iio α) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  rw [Ordinal.mk_Iio_ordinal] at h
  exact Cardinal.lift_le_aleph0.mp h

theorem proposition_3_1_of_ordinal_hasPFP (α : Ordinal.{0})
    (h : HasPFP 𝕜 (OrdinalSpace 𝕜 α)) : Proposition_3_1 𝕜 α := by
  intro _
  letI : Nonempty (OrdinalInterval α) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have hi := uniqueMaximal_of_hasPFP h
  exact ⟨hi.2, fun _ => hi.1⟩

theorem corollary_3_3_of_countable_ordinal_hasPFP
    (hord : ∀ α : Ordinal.{0}, α.card ≤ Cardinal.aleph0 → Ordinal.omega0 ≤ α →
      HasPFP 𝕜 (OrdinalSpace 𝕜 α)) : Corollary_3_3 𝕜 := by
  apply corollary_3_3_of_countablyInfinite
  intro K _ _ _ _
  obtain ⟨α, hα, ⟨e⟩⟩ := countableCompact_infinite_ordinalModel K
  letI : Countable (OrdinalInterval α) := e.symm.injective.countable
  letI : Nonempty (OrdinalInterval α) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  exact (uniqueMaximalClosed_operator_equiv (continuousMapHomeomorphEquiv e)).mpr
    (uniqueMaximal_of_hasPFP (hord α (ordinal_card_le_aleph0_of_countable_interval α) hα)).2

end Posets
