import Posets.OrdinalRankUnitOmegaColouredCores
import Posets.OrdinalClosedCoreOrder

/-! Exact source preimages of the selected ambient compact cores, retaining
the full original finite-power ordinal rank and order type. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜] {ρ : Ordinal.{u}} {hρ : Ordinal.omega0 ≤ ρ}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))}
  {T S : JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))} {N : ℕ} {ε δ : ℝ}

namespace OrdinalRankUnitOmegaColouredCores

variable (F : OrdinalRankUnitOmegaColouredCores ρ hρ M T S N ε δ)

def sourceCore (i : ℕ) : Set (Iic (ordinalRankUnitOmegaSource ρ N (F.index i))) :=
  ordinalRankUnitOmegaSourceEmbedding ρ hρ N (F.index i) ⁻¹' F.core i

def ordinalCore (i : ℕ) : Set Ordinal.{u} := Subtype.val '' F.sourceCore i

theorem sourceCore_compact (i : ℕ) : IsCompact (F.sourceCore i) :=
  ordinalAmbientCore_preimage_compact _
    (ordinalRankUnitOmegaSourceEmbedding_isOpen ρ hρ N (F.index i)) _ (F.compact i)

theorem sourceCore_leaf_closure (i : ℕ) : F.sourceCore i ⊆ closure
    (ordinalAmbientBandLeaves (ordinalRankUnitOmegaSource_top_level ρ hρ N (F.index i))
      (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (F.index i))
      (ordinalRankUnitOmegaSourceEmbedding_isOpen ρ hρ N (F.index i)) M T S
      (ordinalRankUnitOmegaBandLevels ρ N (F.index i+2)) (F.band i).val F.colour ε) := by
  intro x hx
  have h := F.leaf_closure i hx
  rw [ordinalAmbientCore_closure_image _
    (ordinalRankUnitOmegaSourceEmbedding_isOpen ρ hρ N (F.index i))] at h
  exact (ordinalRankUnitOmegaSourceEmbedding_isOpen ρ hρ N (F.index i)).injective.mem_set_image.mp h

theorem sourceCore_rank (i : ℕ) :
    (⟨ordinalRankUnitOmegaSource ρ N (F.index i),
      show ordinalRankUnitOmegaSource ρ N (F.index i) ≤ ordinalRankUnitOmegaSource ρ N (F.index i)
        from le_rfl⟩ : Iic (ordinalRankUnitOmegaSource ρ N (F.index i))) ∈
      ordinalDerived (F.sourceCore i) (ordinalRankUnitOmegaSourceRank ρ N (F.index i)) :=
  (ordinalAmbientCore_rank_preimage_iff _
    (ordinalRankUnitOmegaSourceEmbedding_isOpen ρ hρ N (F.index i)) _ (F.block i) _ _).mpr (F.rank i)

theorem ordinalCore_compact (i : ℕ) : IsCompact (F.ordinalCore i) :=
  (F.sourceCore_compact i).image continuous_subtype_val

theorem ordinalCore_subset (i : ℕ) :
    F.ordinalCore i ⊆ Iic (ordinalRankUnitOmegaSource ρ N (F.index i)) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem ordinalCore_rank (i : ℕ) :
    ordinalRankUnitOmegaSource ρ N (F.index i) ∈
      ordinalDerived (F.ordinalCore i) (ordinalRankUnitOmegaSourceRank ρ N (F.index i)) := by
  rw [ordinalCore, ordinalDerived_image_closedEmbedding isClosed_Iic.isClosedEmbedding_subtypeVal]
  exact mem_image_of_mem Subtype.val (F.sourceCore_rank i)

theorem ordinalCore_type_lower (i : ℕ) :
    Ordinal.lift.{u+1} (Order.succ (ordinalRankUnitOmegaSource ρ N (F.index i))) ≤
      Ordinal.type (· < · : F.ordinalCore i → _ → Prop) := by
  have hRank : ordinalRankUnitOmegaSourceRank ρ N (F.index i) ≠ 0 := by
    apply mul_ne_zero (Ordinal.omega0_pos.trans_le hρ).ne'
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos N) (by omega : 0 < F.index i + 2)).ne'
  have ht := ordinalClosedCore_order_type_lower (F.sourceCore i) (F.sourceCore_compact i)
    hRank ⟨_, F.sourceCore_rank i⟩
  simpa only [ordinalRankUnitOmegaSourceRank, Ordinal.opow_mul,
    ordinalRankUnitOmegaSource, ordinalRankUnitOmegaBase, ordinalCore] using ht

end OrdinalRankUnitOmegaColouredCores
end Posets

