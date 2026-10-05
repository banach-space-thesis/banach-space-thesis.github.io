import Posets.OrdinalVariableUnitColouredGeometry
import Posets.OrdinalClosedCopySeparatedAmbientGeometry
import Posets.OrdinalRegularOmegaAssemblyPrefix
import Posets.OrdinalAmbientCoreBandsRestriction

/-! Actual ambient cells and prefix coordinates for arbitrary ordinal rank
units, after losing one finite coefficient. The reading sections
remain inside the selected compact cores. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜] {γ : Ordinal.{u}} {N : ℕ} {P : OrdinalVariableUnitParameters γ N}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ))}
  {T S : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))} {ε δ : ℝ}

namespace OrdinalVariableUnitColouredCores

variable (F : OrdinalVariableUnitColouredCores P M T S ε δ)

def selectedH (i : ℕ) : Set (Iio (Ordinal.omega0 ^ γ)) :=
  ordinalSeparatedBandAmbientSet (F.bandGeometry i) (P.embedding (F.index i))

theorem selectedH_compact (i : ℕ) : IsCompact (F.selectedH i) :=
  ordinalSeparatedBandAmbientSet_isCompact _ _ (P.embedding_isOpen (F.index i))

instance selectedH_compactSpace (i : ℕ) : CompactSpace (F.selectedH i) :=
  isCompact_iff_compactSpace.mp (F.selectedH_compact i)

theorem selectedH_clopen (i : ℕ) : IsClopen (F.selectedH i) :=
  ordinalSeparatedBandAmbientSet_isClopen _ _ (P.embedding_isOpen (F.index i))

theorem selectedH_block (i : ℕ) :
    F.selectedH i ⊆ range (P.embedding (F.index i)) :=
  ordinalSeparatedBandAmbientSet_subset_range _ _

theorem selectedH_disjoint : Pairwise (fun i j => Disjoint (F.selectedH i) (F.selectedH j)) := by
  intro i j hij
  have hd := P.outerBlock_disjoint (F.strictMono.injective.ne hij)
  exact hd.mono (F.selectedH_block i) (F.selectedH_block j)

def selectedModel (i : ℕ) := OrdinalInterval (Ordinal.omega0 ^ P.sourceUnit (F.index i))

def selectedP (i : ℕ) : C(F.selectedH i, F.selectedModel i) :=
  ordinalOmegaPrefixCoordinate (F.bandGeometry i).model
    (ordinalSeparatedBandAmbientCoordinate (F.bandGeometry i)
      (P.embedding (F.index i))
      (P.embedding_isOpen (F.index i))) _

def selectedQ (i : ℕ) : C(F.selectedModel i, F.selectedH i) :=
  ordinalOmegaPrefixSection (F.bandGeometry i).model
    (ordinalSeparatedBandAmbientSection (F.bandGeometry i)
      (P.embedding (F.index i))
      (P.embedding_isOpen (F.index i)))
    (F.bandGeometry_model_large i)

theorem selected_section (i : ℕ) : Function.RightInverse (F.selectedQ i) (F.selectedP i) :=
  ordinalOmegaPrefix_section _ _ _ (ordinalSeparatedBandAmbientSection_rightInverse _ _ _) _

def sourceLeaves (i : ℕ) : Set (Iic (P.source (F.index i))) :=
  ordinalAmbientBandLeaves (P.source_top_level (F.index i))
    (P.embedding (F.index i))
    (P.embedding_isOpen (F.index i)) M T S
    (F.bandLevels i) (F.band i).val F.colour ε

def selectedLeaves (i : ℕ) : Set (Iio (Ordinal.omega0 ^ γ)) :=
  (P.embedding (F.index i) '' F.sourceLeaves i) ∩ F.selectedH i

theorem selectedLeaves_subset (i : ℕ) : F.selectedLeaves i ⊆ F.selectedH i :=
  inter_subset_right

theorem selectedQ_core (i : ℕ) (x : F.selectedModel i) : (F.selectedQ i x).val ∈ F.core i := by
  have h := ordinalSeparatedBandAmbientSection_core (F.bandGeometry i)
    (P.embedding (F.index i))
    (P.embedding_isOpen (F.index i))
    ((F.bandGeometry i).model (ordinalOmegaPrefixInclusion (F.bandGeometry_model_large i) x))
  change (F.selectedQ i x).val ∈
    P.embedding (F.index i) ''
      ((Subtype.val : Iic (P.source (F.index i)) → Ordinal.{u}) ⁻¹'
        F.ordinalCore i) at h
  obtain ⟨z, hz, hzx⟩ := h
  rw [← hzx]
  obtain ⟨w, hw, heq⟩ := hz
  have heq' : w = z := Subtype.ext heq
  exact heq' ▸ hw

theorem selectedQ_leaf_closure (i : ℕ) (x : F.selectedModel i) :
    (F.selectedQ i x).val ∈ closure (F.selectedLeaves i) := by
  apply ordinalSeparatedBandAmbientSection_leaf_closure (F.bandGeometry i)
    (P.embedding (F.index i))
    (P.embedding_isOpen (F.index i)) (F.sourceLeaves i)
  exact image_mono (F.sourceCore_leaf_closure i)

def selectedV (i : ℕ) (y : Iio (Ordinal.omega0 ^ γ)) : Set (Iio (Ordinal.omega0 ^ γ)) :=
  ordinalAmbientCeilingCellAt (P.embedding (F.index i))
    (F.bandLevels i (F.band i).val).val y

theorem selectedH_upper_cell (i : ℕ) :
    F.selectedH i = P.embedding (F.index i) ''
      ordinalTowerCell (P.source (F.index i))
        (ordinalTowerLevel (P.source (F.index i))
          (F.bandLevels i ((F.band i).val+1)).val)
        (F.bandGeometry i).upperPoint.val := by
  change _ '' ((Subtype.val : Iic (P.source (F.index i)) → Ordinal.{u}) ⁻¹'
    (F.bandGeometry i).H) = _
  rw [F.bandGeometry_cell_eq i]
  congr 1
  ext x
  change (x.val ≤ P.source (F.index i) ∧ _) ↔ _
  exact and_iff_right x.property

theorem selectedLeaves_upper_image (i : ℕ) :
    F.selectedLeaves i = P.embedding (F.index i) ''
      (F.sourceLeaves i ∩ ordinalTowerCell (P.source (F.index i))
        (ordinalTowerLevel (P.source (F.index i))
          (F.bandLevels i ((F.band i).val+1)).val)
        (F.bandGeometry i).upperPoint.val) := by
  rw [selectedLeaves, F.selectedH_upper_cell i]
  exact (image_inter (P.embedding_isOpen (F.index i)).injective).symm

end OrdinalVariableUnitColouredCores
end Posets





