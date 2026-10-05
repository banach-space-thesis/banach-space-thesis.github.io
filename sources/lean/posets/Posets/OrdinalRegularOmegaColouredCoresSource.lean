import Posets.OrdinalRegularOmegaColouredCores
import Posets.OrdinalClosedCoreOrder

/-! Exact source preimages of the selected ambient compact cores, retaining
the full original finite-power ordinal rank and order type. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜] {c : Cardinal.{u}} {hc : Cardinal.aleph0 < c}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (c.ord ^ Ordinal.omega0))}
  {T S : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))} {N : ℕ} {ε δ : ℝ}

namespace OrdinalRegularOmegaColouredCores

variable (F : OrdinalRegularOmegaColouredCores c hc M T S N ε δ)

def sourceCore (i : ℕ) : Set (Iic (ordinalRegularOmegaSource c N (F.index i))) :=
  ordinalRegularOmegaSourceEmbedding c hc N (F.index i) ⁻¹' F.core i

def ordinalCore (i : ℕ) : Set Ordinal.{u} := Subtype.val '' F.sourceCore i

theorem sourceCore_compact (i : ℕ) : IsCompact (F.sourceCore i) :=
  ordinalAmbientCore_preimage_compact _
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)) _ (F.compact i)

theorem sourceCore_leaf_closure (i : ℕ) : F.sourceCore i ⊆ closure
    (ordinalAmbientBandLeaves (ordinalRegularOmegaSource_top_level c hc N (F.index i))
      (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
      (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)) M T S
      (ordinalRegularOmegaBandLevels c N (F.index i+2)) (F.band i).val F.colour ε) := by
  intro x hx
  have h := F.leaf_closure i hx
  rw [ordinalAmbientCore_closure_image _
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i))] at h
  exact (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)).injective.mem_set_image.mp h

theorem sourceCore_rank (i : ℕ) :
    (⟨ordinalRegularOmegaSource c N (F.index i),
      show ordinalRegularOmegaSource c N (F.index i) ≤ ordinalRegularOmegaSource c N (F.index i)
        from le_rfl⟩ : Iic (ordinalRegularOmegaSource c N (F.index i))) ∈
      ordinalDerived (F.sourceCore i) (ordinalRegularOmegaSourceRank c N (F.index i)) :=
  (ordinalAmbientCore_rank_preimage_iff _
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)) _ (F.block i) _ _).mpr (F.rank i)

theorem ordinalCore_compact (i : ℕ) : IsCompact (F.ordinalCore i) :=
  (F.sourceCore_compact i).image continuous_subtype_val

theorem ordinalCore_subset (i : ℕ) :
    F.ordinalCore i ⊆ Iic (ordinalRegularOmegaSource c N (F.index i)) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem ordinalCore_rank (i : ℕ) :
    ordinalRegularOmegaSource c N (F.index i) ∈
      ordinalDerived (F.ordinalCore i) (ordinalRegularOmegaSourceRank c N (F.index i)) := by
  rw [ordinalCore, ordinalDerived_image_closedEmbedding isClosed_Iic.isClosedEmbedding_subtypeVal]
  exact mem_image_of_mem Subtype.val (F.sourceCore_rank i)

theorem ordinalCore_type_lower (i : ℕ) :
    Ordinal.lift.{u+1} (Order.succ (ordinalRegularOmegaSource c N (F.index i))) ≤
      Ordinal.type (· < · : F.ordinalCore i → _ → Prop) := by
  have hρ : ordinalRegularOmegaSourceRank c N (F.index i) ≠ 0 := by
    apply mul_ne_zero (Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le)).ne'
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos N) (by omega : 0 < F.index i + 2)).ne'
  have ht := ordinalClosedCore_order_type_lower (F.sourceCore i) (F.sourceCore_compact i)
    hρ ⟨_, F.sourceCore_rank i⟩
  simpa only [ordinalRegularOmegaSourceRank, ordinal_uncountable_initial_power_rank hc,
    ordinalRegularOmegaSource, ordinalCore] using ht

end OrdinalRegularOmegaColouredCores
end Posets
