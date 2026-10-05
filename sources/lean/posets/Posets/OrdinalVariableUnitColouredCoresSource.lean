import Posets.OrdinalVariableUnitColouredCores
import Posets.OrdinalClosedCoreOrder

/-! Source preimages retain the full varying rank and actual ordinal type. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜] {γ : Ordinal.{u}} {N : ℕ}
  {P : OrdinalVariableUnitParameters γ N}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ))}
  {T S : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))} {ε δ : ℝ}

namespace OrdinalVariableUnitColouredCores
variable (F : OrdinalVariableUnitColouredCores P M T S ε δ)

def sourceCore (i : ℕ) : Set (Iic (P.source (F.index i))) := P.embedding (F.index i) ⁻¹' F.core i
def ordinalCore (i : ℕ) : Set Ordinal.{u} := Subtype.val '' F.sourceCore i

theorem sourceCore_compact (i : ℕ) : IsCompact (F.sourceCore i) :=
  ordinalAmbientCore_preimage_compact _ (P.embedding_isOpen (F.index i)) _ (F.compact i)

theorem sourceCore_leaf_closure (i : ℕ) : F.sourceCore i ⊆ closure
    (ordinalAmbientBandLeaves (P.source_top_level (F.index i))
      (P.embedding (F.index i)) (P.embedding_isOpen (F.index i)) M T S
      (P.bandLevels (F.index i)) (F.band i).val F.colour ε) := by
  intro x hx
  have h := F.leaf_closure i hx
  rw [ordinalAmbientCore_closure_image _ (P.embedding_isOpen (F.index i))] at h
  exact (P.embedding_isOpen (F.index i)).injective.mem_set_image.mp h

theorem sourceCore_rank (i : ℕ) :
    (⟨P.source (F.index i), show P.source (F.index i) ≤ P.source (F.index i)
      from le_rfl⟩ : Iic (P.source (F.index i))) ∈
      ordinalDerived (F.sourceCore i) (P.sourceRank (F.index i)) :=
  (ordinalAmbientCore_rank_preimage_iff _ (P.embedding_isOpen (F.index i))
    _ (F.block i) _ _).mpr (F.rank i)

theorem ordinalCore_compact (i : ℕ) : IsCompact (F.ordinalCore i) :=
  (F.sourceCore_compact i).image continuous_subtype_val

theorem ordinalCore_subset (i : ℕ) : F.ordinalCore i ⊆ Iic (P.source (F.index i)) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem ordinalCore_rank (i : ℕ) :
    P.source (F.index i) ∈ ordinalDerived (F.ordinalCore i) (P.sourceRank (F.index i)) := by
  rw [ordinalCore, ordinalDerived_image_closedEmbedding isClosed_Iic.isClosedEmbedding_subtypeVal]
  exact mem_image_of_mem Subtype.val (F.sourceCore_rank i)

theorem ordinalCore_type_lower (i : ℕ) :
    Ordinal.lift.{u+1} (Order.succ (P.source (F.index i))) ≤
      Ordinal.type (· < · : F.ordinalCore i → _ → Prop) := by
  have ht := ordinalClosedCore_order_type_lower (F.sourceCore i) (F.sourceCore_compact i)
    (P.outerRank_pos (F.index i+1)).ne' ⟨_, F.sourceCore_rank i⟩
  simpa only [OrdinalVariableUnitParameters.source, ordinalCore] using ht

end OrdinalVariableUnitColouredCores
end Posets
