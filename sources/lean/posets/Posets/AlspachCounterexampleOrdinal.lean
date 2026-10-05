import Posets.AlspachCounterexampleRankOmega
import Posets.AlspachCounterexampleOrdinalModel

/-! Actual homeomorphisms of the ω-stage point and row spaces onto the
ordinal interval [0, ω^(ω²)], obtained from their calculated derivatives. -/

noncomputable section
open Set Topology ThesisCommon
open scoped Ordinal
namespace Posets
universe u v
variable {𝕜 : Type v} [RCLike 𝕜]

theorem alspach_ordinalInterval_power_ordinalDerived (η : Ordinal.{0}) (hη : η ≠ 0) :
    ordinalDerived (univ : Set (OrdinalInterval (ω ^ η))) η =
      {⟨ω ^ η, Ordinal.zero_le _, le_rfl⟩} := by
  have hIcc : Icc (0 : Ordinal.{0}) (ω ^ η) = Iic (ω ^ η) := by ext x; simp
  have h := ordinalDerived_image_closedEmbedding
    (isClosed_Icc : IsClosed (Icc (0 : Ordinal.{0}) (ω ^ η))).isClosedEmbedding_subtypeVal univ η
  rw [image_univ, Subtype.range_coe] at h
  have hi : {ω ^ η} = (Subtype.val : OrdinalInterval (ω ^ η) → Ordinal.{0}) ''
      ordinalDerived univ η := by
    calc
      {ω ^ η} = ordinalDerived (Iic (ω ^ η)) η := (ordinalDerived_Iic_power_self hη).symm
      _ = ordinalDerived (Icc (0 : Ordinal.{0}) (ω ^ η)) η :=
        congrArg (fun S => ordinalDerived S η) hIcc.symm
      _ = _ := h
  apply (Set.image_injective.mpr (Subtype.val_injective :
    Function.Injective (Subtype.val : OrdinalInterval (ω ^ η) → Ordinal.{0})))
  rw [image_singleton]
  exact hi.symm

def alspachOmegaCompactRows_pointHomeomorph
    (B : Type u) [TopologicalSpace B] [CompactSpace B] [T2Space B] [Countable B]
    (p : B) (hB : ordinalDerived (univ : Set B) (ω : Ordinal.{0}) = {p}) :
    (alspachOmegaCompactRows (𝕜 := 𝕜) B p).Point ≃ₜ
      OrdinalInterval (ω ^ (ω ^ (2 : Ordinal.{0}))) :=
  Classical.choice (alspach_countable_compact_singleton_homeomorph _
    (alspachOmegaCompactRows (𝕜 := 𝕜) B p).rows.point _
    (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
    (alspachOmegaCompactRows_ordinalDerived B p hB).1)

def alspachOmegaCompactRows_indexHomeomorph
    (B : Type u) [TopologicalSpace B] [CompactSpace B] [T2Space B] [Countable B]
    (p : B) (hB : ordinalDerived (univ : Set B) (ω : Ordinal.{0}) = {p}) :
    (alspachOmegaCompactRows (𝕜 := 𝕜) B p).Index ≃ₜ
      OrdinalInterval (ω ^ (ω ^ (2 : Ordinal.{0}))) :=
  Classical.choice (alspach_countable_compact_singleton_homeomorph _
    (alspachOmegaCompactRows (𝕜 := 𝕜) B p).rows.index _
    (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
    (alspachOmegaCompactRows_ordinalDerived B p hB).2)

end Posets
