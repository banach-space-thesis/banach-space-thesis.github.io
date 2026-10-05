import Posets.OrdinalOmegaColouredGeometry
import Posets.OrdinalClosedCopySeparatedAmbientGeometry
import Posets.OrdinalRegularOmegaAssemblyPrefix
import Posets.OrdinalAmbientCoreBandsRestriction

/-! Actual ambient cells and prefix coordinates for arbitrary uncountable
initial ordinals, after losing one finite exponent. The reading sections
remain inside the selected compact cores. -/

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

def lossSelectedH (i : ℕ) : Set (Iio (c.ord ^ Ordinal.omega0)) :=
  ordinalSeparatedBandAmbientSet (F.lossGeometry i) (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))

theorem lossSelectedH_compact (i : ℕ) : IsCompact (F.lossSelectedH i) :=
  ordinalSeparatedBandAmbientSet_isCompact _ _ (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i))

instance lossSelectedH_compactSpace (i : ℕ) : CompactSpace (F.lossSelectedH i) :=
  isCompact_iff_compactSpace.mp (F.lossSelectedH_compact i)

theorem lossSelectedH_clopen (i : ℕ) : IsClopen (F.lossSelectedH i) :=
  ordinalSeparatedBandAmbientSet_isClopen _ _ (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i))

theorem lossSelectedH_block (i : ℕ) :
    F.lossSelectedH i ⊆ range (ordinalRegularOmegaSourceEmbedding c hc N (F.index i)) :=
  ordinalSeparatedBandAmbientSet_subset_range _ _

theorem lossSelectedH_disjoint : Pairwise (fun i j => Disjoint (F.lossSelectedH i) (F.lossSelectedH j)) := by
  intro i j hij
  have hd := ordinalRegularOmegaOuterFamily_disjoint c hc.le
    (ordinalRegularOmegaOuterHeight N) (ordinalRegularOmegaOuterHeight_strictMono N)
    (F.strictMono.injective.ne hij)
  exact hd.mono (F.lossSelectedH_block i) (F.lossSelectedH_block j)

def lossSelectedModel (i : ℕ) := OrdinalInterval (c.ord ^ ((F.index i+1 : ℕ) : Ordinal))

def lossSelectedP (i : ℕ) : C(F.lossSelectedH i, F.lossSelectedModel i) :=
  ordinalOmegaPrefixCoordinate (F.lossGeometry i).model
    (ordinalSeparatedBandAmbientCoordinate (F.lossGeometry i)
      (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
      (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i))) _

def lossSelectedQ (i : ℕ) : C(F.lossSelectedModel i, F.lossSelectedH i) :=
  ordinalOmegaPrefixSection (F.lossGeometry i).model
    (ordinalSeparatedBandAmbientSection (F.lossGeometry i)
      (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
      (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)))
    (F.lossGeometry_model_large i)

theorem lossSelected_section (i : ℕ) : Function.RightInverse (F.lossSelectedQ i) (F.lossSelectedP i) :=
  ordinalOmegaPrefix_section _ _ _ (ordinalSeparatedBandAmbientSection_rightInverse _ _ _) _

def lossSourceLeaves (i : ℕ) : Set (Iic (ordinalRegularOmegaSource c N (F.index i))) :=
  ordinalAmbientBandLeaves (ordinalRegularOmegaSource_top_level c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)) M T S
    (ordinalRegularOmegaBandLevels c N (F.index i+2)) (F.band i).val F.colour ε

def lossSelectedLeaves (i : ℕ) : Set (Iio (c.ord ^ Ordinal.omega0)) :=
  (ordinalRegularOmegaSourceEmbedding c hc N (F.index i) '' F.lossSourceLeaves i) ∩ F.lossSelectedH i

theorem lossSelectedLeaves_subset (i : ℕ) : F.lossSelectedLeaves i ⊆ F.lossSelectedH i :=
  inter_subset_right

theorem lossSelectedQ_core (i : ℕ) (x : F.lossSelectedModel i) : (F.lossSelectedQ i x).val ∈ F.core i := by
  have h := ordinalSeparatedBandAmbientSection_core (F.lossGeometry i)
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i))
    ((F.lossGeometry i).model (ordinalOmegaPrefixInclusion (F.lossGeometry_model_large i) x))
  change (F.lossSelectedQ i x).val ∈
    ordinalRegularOmegaSourceEmbedding c hc N (F.index i) ''
      ((Subtype.val : Iic (ordinalRegularOmegaSource c N (F.index i)) → Ordinal.{u}) ⁻¹'
        F.ordinalCore i) at h
  obtain ⟨z, hz, hzx⟩ := h
  rw [← hzx]
  obtain ⟨w, hw, heq⟩ := hz
  have heq' : w = z := Subtype.ext heq
  exact heq' ▸ hw

theorem lossSelectedQ_leaf_closure (i : ℕ) (x : F.lossSelectedModel i) :
    (F.lossSelectedQ i x).val ∈ closure (F.lossSelectedLeaves i) := by
  apply ordinalSeparatedBandAmbientSection_leaf_closure (F.lossGeometry i)
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)) (F.lossSourceLeaves i)
  exact image_mono (F.sourceCore_leaf_closure i)

def lossSelectedV (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0)) : Set (Iio (c.ord ^ Ordinal.omega0)) :=
  ordinalAmbientCeilingCellAt (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaBandLevels c N (F.index i+2) (F.band i).val).val y

theorem lossSelectedH_upper_cell (i : ℕ) :
    F.lossSelectedH i = ordinalRegularOmegaSourceEmbedding c hc N (F.index i) ''
      ordinalTowerCell (ordinalRegularOmegaSource c N (F.index i))
        (ordinalTowerLevel (ordinalRegularOmegaSource c N (F.index i))
          (ordinalRegularOmegaBandLevels c N (F.index i+2) ((F.band i).val+1)).val)
        (F.lossGeometry i).upperPoint.val := by
  change _ '' ((Subtype.val : Iic (ordinalRegularOmegaSource c N (F.index i)) → Ordinal.{u}) ⁻¹'
    (F.lossGeometry i).H) = _
  rw [F.lossGeometry_cell_eq i]
  congr 1
  ext x
  change (x.val ≤ ordinalRegularOmegaSource c N (F.index i) ∧ _) ↔ _
  exact and_iff_right x.property

theorem lossSelectedLeaves_upper_image (i : ℕ) :
    F.lossSelectedLeaves i = ordinalRegularOmegaSourceEmbedding c hc N (F.index i) ''
      (F.lossSourceLeaves i ∩ ordinalTowerCell (ordinalRegularOmegaSource c N (F.index i))
        (ordinalTowerLevel (ordinalRegularOmegaSource c N (F.index i))
          (ordinalRegularOmegaBandLevels c N (F.index i+2) ((F.band i).val+1)).val)
        (F.lossGeometry i).upperPoint.val) := by
  rw [lossSelectedLeaves, F.lossSelectedH_upper_cell i]
  exact (image_inter (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)).injective).symm

end OrdinalRegularOmegaColouredCores
end Posets

