import Posets.OrdinalRegularOmegaColouredGeometry
import Posets.OrdinalClosedCopyAmbientGeometry
import Posets.OrdinalRegularOmegaAssemblyPrefix
import Posets.OrdinalAmbientCoreBandsRestriction

/-! Actual ambient cells and prefix coordinate maps for the selected cores.
Every reading section stays in its selected compact core. -/

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

variable (F : OrdinalRegularOmegaColouredCores c hc M T S N ε δ) (hr : c.IsRegular)

def selectedH (i : ℕ) : Set (Iio (c.ord ^ Ordinal.omega0)) :=
  ordinalBandAmbientSet (F.bandGeometry hr i) (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))

theorem selectedH_compact (i : ℕ) : IsCompact (F.selectedH hr i) :=
  ordinalBandAmbientSet_isCompact _ _ (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i))

instance selectedH_compactSpace (i : ℕ) : CompactSpace (F.selectedH hr i) :=
  isCompact_iff_compactSpace.mp (F.selectedH_compact hr i)

theorem selectedH_clopen (i : ℕ) : IsClopen (F.selectedH hr i) :=
  ordinalBandAmbientSet_isClopen _ _ (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i))

theorem selectedH_block (i : ℕ) :
    F.selectedH hr i ⊆ range (ordinalRegularOmegaSourceEmbedding c hc N (F.index i)) :=
  ordinalBandAmbientSet_subset_range _ _

theorem selectedH_disjoint : Pairwise (fun i j => Disjoint (F.selectedH hr i) (F.selectedH hr j)) := by
  intro i j hij
  have hd := ordinalRegularOmegaOuterFamily_disjoint c hc.le
    (ordinalRegularOmegaOuterHeight N) (ordinalRegularOmegaOuterHeight_strictMono N)
    (F.strictMono.injective.ne hij)
  exact hd.mono (F.selectedH_block hr i) (F.selectedH_block hr j)

def selectedModel (i : ℕ) := OrdinalInterval (c.ord ^ ((F.index i+2 : ℕ) : Ordinal))

def selectedP (i : ℕ) : C(F.selectedH hr i, F.selectedModel i) :=
  ordinalOmegaPrefixCoordinate (F.bandGeometry hr i).model
    (ordinalBandAmbientCoordinate (F.bandGeometry hr i)
      (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
      (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i))) _

def selectedQ (i : ℕ) : C(F.selectedModel i, F.selectedH hr i) :=
  ordinalOmegaPrefixSection (F.bandGeometry hr i).model
    (ordinalBandAmbientSection (F.bandGeometry hr i)
      (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
      (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)))
    (F.bandGeometry_model_large hr i)

theorem selected_section (i : ℕ) : Function.RightInverse (F.selectedQ hr i) (F.selectedP hr i) :=
  ordinalOmegaPrefix_section _ _ _ (ordinalBandAmbientSection_rightInverse _ _ _) _

def sourceLeaves (i : ℕ) : Set (Iic (ordinalRegularOmegaSource c N (F.index i))) :=
  ordinalAmbientBandLeaves (ordinalRegularOmegaSource_top_level c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)) M T S
    (ordinalRegularOmegaBandLevels c N (F.index i+2)) (F.band i).val F.colour ε

def selectedLeaves (i : ℕ) : Set (Iio (c.ord ^ Ordinal.omega0)) :=
  (ordinalRegularOmegaSourceEmbedding c hc N (F.index i) '' F.sourceLeaves i) ∩ F.selectedH hr i

theorem selectedLeaves_subset (i : ℕ) : F.selectedLeaves hr i ⊆ F.selectedH hr i :=
  inter_subset_right

theorem selectedQ_core (i : ℕ) (x : F.selectedModel i) : (F.selectedQ hr i x).val ∈ F.core i := by
  have h := ordinalBandAmbientSection_core (F.bandGeometry hr i)
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i))
    ((F.bandGeometry hr i).model (ordinalOmegaPrefixInclusion (F.bandGeometry_model_large hr i) x))
  change (F.selectedQ hr i x).val ∈
    ordinalRegularOmegaSourceEmbedding c hc N (F.index i) ''
      ((Subtype.val : Iic (ordinalRegularOmegaSource c N (F.index i)) → Ordinal.{u}) ⁻¹'
        F.ordinalCore i) at h
  obtain ⟨z, hz, hzx⟩ := h
  rw [← hzx]
  obtain ⟨w, hw, heq⟩ := hz
  have heq' : w = z := Subtype.ext heq
  exact heq' ▸ hw

theorem selectedQ_leaf_closure (i : ℕ) (x : F.selectedModel i) :
    (F.selectedQ hr i x).val ∈ closure (F.selectedLeaves hr i) := by
  apply ordinalBandAmbientSection_leaf_closure (F.bandGeometry hr i)
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)) (F.sourceLeaves i)
  exact image_mono (F.sourceCore_leaf_closure i)

def selectedV (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0)) : Set (Iio (c.ord ^ Ordinal.omega0)) :=
  ordinalAmbientCeilingCellAt (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaBandLevels c N (F.index i+2) (F.band i).val).val y

theorem selectedH_upper_cell (i : ℕ) :
    F.selectedH hr i = ordinalRegularOmegaSourceEmbedding c hc N (F.index i) ''
      ordinalTowerCell (ordinalRegularOmegaSource c N (F.index i))
        (ordinalTowerLevel (ordinalRegularOmegaSource c N (F.index i))
          (ordinalRegularOmegaBandLevels c N (F.index i+2) ((F.band i).val+1)).val)
        (F.bandGeometry hr i).upperPoint.val := by
  change _ '' ((Subtype.val : Iic (ordinalRegularOmegaSource c N (F.index i)) → Ordinal.{u}) ⁻¹'
    (F.bandGeometry hr i).H) = _
  rw [F.bandGeometry_cell_eq hr i]
  congr 1
  ext x
  change (x.val ≤ ordinalRegularOmegaSource c N (F.index i) ∧ _) ↔ _
  exact and_iff_right x.property

theorem selectedLeaves_upper_image (i : ℕ) :
    F.selectedLeaves hr i = ordinalRegularOmegaSourceEmbedding c hc N (F.index i) ''
      (F.sourceLeaves i ∩ ordinalTowerCell (ordinalRegularOmegaSource c N (F.index i))
        (ordinalTowerLevel (ordinalRegularOmegaSource c N (F.index i))
          (ordinalRegularOmegaBandLevels c N (F.index i+2) ((F.band i).val+1)).val)
        (F.bandGeometry hr i).upperPoint.val) := by
  rw [selectedLeaves, F.selectedH_upper_cell hr i]
  exact (image_inter (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)).injective).symm

end OrdinalRegularOmegaColouredCores
end Posets
