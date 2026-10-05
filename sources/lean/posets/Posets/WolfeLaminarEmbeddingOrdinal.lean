import Posets.OrdinalLiftFinite
import Posets.WolfeLaminarEmbedding
import Posets.AlspachCounterexampleOrdinalOperator

/-! A nonempty positive derivative of a countable compact space gives an
actual isometric copy of the corresponding ordinal function space. -/
noncomputable section
open Set Topology ThesisCommon
open scoped Ordinal
namespace Posets
set_option maxHeartbeats 800000
variable {𝕜 : Type} [RCLike 𝕜]

def ordinalInitialClosedCopy {α β : Ordinal.{0}} (h : β ≤ α) : OrdinalClosedCopy α β :=
  ⟨⟨fun x => ⟨x.val, x.property.1, x.property.2.trans h⟩,
    continuous_subtype_val.subtype_mk _⟩,
    fun x y he => Subtype.ext (congrArg (fun z : OrdinalInterval α => z.val) he)⟩

def ordinalCopyInsertIsometry {α β : Ordinal.{0}} (e : OrdinalClosedCopy α β) :
    OrdinalContinuous 𝕜 β →ₗᵢ[𝕜] OrdinalContinuous 𝕜 α where
  __ := (ordinalCopyInsert (𝕜 := 𝕜) e).toLinearMap
  norm_map' f := by
    apply le_antisymm
    · exact ((ordinalCopyInsert (𝕜 := 𝕜) e).le_opNorm f).trans
        (by simpa using mul_le_mul_of_nonneg_right (norm_ordinalCopyInsert_le (𝕜 := 𝕜) e) (norm_nonneg f))
    · have he : ordinalCopyRead e (ordinalCopyInsert (𝕜 := 𝕜) e f) = f :=
        DFunLike.congr_fun (ordinalCopyRead_comp_insert (𝕜 := 𝕜) e) f
      calc
        ‖f‖ = ‖ordinalCopyRead e (ordinalCopyInsert (𝕜 := 𝕜) e f)‖ := congrArg norm he.symm
        _ ≤ ‖ordinalCopyRead (𝕜 := 𝕜) e‖ * ‖ordinalCopyInsert (𝕜 := 𝕜) e f‖ :=
          (ordinalCopyRead (𝕜 := 𝕜) e).le_opNorm _
        _ ≤ ‖ordinalCopyInsert (𝕜 := 𝕜) e f‖ := by
          simpa using mul_le_mul_of_nonneg_right (norm_ordinalCopyRead_le (𝕜 := 𝕜) e) (norm_nonneg _)

theorem exists_ordinal_isometry_of_derivative_nonempty (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [Countable K]
    {α : Ordinal.{0}} (hα : α ≠ 0)
    (hD : (ordinalDerived (univ : Set K) α).Nonempty) :
    Nonempty (OrdinalContinuous 𝕜 (ω ^ α) →ₗᵢ[𝕜] C(K, 𝕜)) := by
  letI instNonemptyK : Nonempty K := ⟨hD.choose⟩
  obtain ⟨θ, ⟨e⟩⟩ := alspach_countable_compact_ordinalModel K
  let f : K → Ordinal.{0} := fun x => (e x).val
  have hf : IsClosedEmbedding f :=
    (isClosed_Icc : IsClosed (Icc (0 : Ordinal.{0}) θ)).isClosedEmbedding_subtypeVal.comp
      e.isClosedEmbedding
  have hI : f '' univ = Iic θ := by
    rw [← image_image]
    simp only [image_univ, e.surjective.range_eq, Subtype.range_coe]
    ext x
    simp
  have hd := ordinalDerived_image_closedEmbedding hf univ α
  rw [hI] at hd
  have hle : (ω : Ordinal.{0}) ^ α ≤ θ := ordinal_power_le_of_nonempty_derivative hα
    (by rw [hd]; exact hD.image f)
  exact ⟨(alspachContinuousHomeomorphIsometry (𝕜 := 𝕜) e.symm).toLinearIsometry.comp
    (ordinalCopyInsertIsometry (ordinalInitialClosedCopy hle))⟩

end Posets


