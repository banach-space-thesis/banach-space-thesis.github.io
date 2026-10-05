import Sigma.ComplexCodeAtomicRows
import Sigma.ComplexAdaptiveConstruction
import Sigma.HistoryCharges
import ThesisCommon.Analysis.SigmaComplexChargeSeries
import Sigma.ReservedStock
import ThesisCommon.Analysis.ChargeSeries
import ThesisCommon.Analysis.ChargePushforward

/-! Concrete full-power-set charges computed from the earlier splitting
history. The scheduled support condition proves exact agreement with the
charge computed from the final history, on every subset of the paired base. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] Classical.propDecidable

def ComplexThreeLevelChoice.piece {μ : ComplexAtomicRows} {R : Set ℕ} (d : ComplexThreeLevelChoice μ R) : Bool → Set Point
  | false => d.Z
  | true => cylinder d.J₁ \ d.Z

theorem ComplexThreeLevelChoice.piece_infinite {μ : ComplexAtomicRows} {R : Set ℕ}
    (d : ComplexThreeLevelChoice μ R) (bit : Bool) : (d.piece bit).Infinite := by
  have hJ := d.infinite_J₂.mono d.J₂_subset
  cases bit
  · exact d.splits.infinite hJ
  · exact d.splits.other.infinite hJ

def ComplexThreeLevelChoice.pieceCharge {μ : ComplexAtomicRows} {R : Set ℕ}
    (d : ComplexThreeLevelChoice μ R) (bit : Bool) : UnitCharge Point :=
  ultrafilterCharge (freeUltrafilterOn (d.piece bit) (d.piece_infinite bit))

def complexHistoryFamilyCharge {μ μt : ConstructionIndex → ComplexAtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (a : ConstructionIndex)
    (h : ∀ i, i < a → ComplexCodedStage (μ i) (μt i) (R i) (Rt i))
    (side : Bool) (i : ConstructionIndex) (bit : Bool) : UnitCharge Point :=
  if hi : i < a then
    if side then (h i hi).choices.2.pieceCharge bit else (h i hi).choices.1.pieceCharge bit
  else 0

def complexFinalFamilyCharge {μ μt : ConstructionIndex → ComplexAtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (d : ComplexCodedConstruction μ μt R Rt)
    (side : Bool) (i : ConstructionIndex) (bit : Bool) : UnitCharge Point :=
  if side then (d i).choices.2.pieceCharge bit else (d i).choices.1.pieceCharge bit

def complexIndexedCodeCharge (Uinf : Ultrafilter Point)
    (F : Bool → ConstructionIndex → Bool → UnitCharge Point)
    (c : lp (fun _ : FullAtom => ℂ) 1) (hc : ‖c‖ ≤ 1) : ComplexPairedMeasure :=
  complexLpChargeSeries c hc (fun p => (indexedAtomCharge Uinf F p).toComplex)

theorem complexHistoryCodeCharge_eq_final {μ μt : ConstructionIndex → ComplexAtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (d : ComplexCodedConstruction μ μt R Rt)
    (a : ConstructionIndex) (Uinf : Ultrafilter Point)
    (c : lp (fun _ : FullAtom => ℂ) 1) (hc : ‖c‖ ≤ 1)
    (hsupport : ∀ side bit i, a ≤ i → c (familyAtom side bit i) = 0) :
    complexIndexedCodeCharge Uinf (complexHistoryFamilyCharge a (fun i _ => d i)) c hc =
      complexIndexedCodeCharge Uinf (complexFinalFamilyCharge d) c hc := by
  apply ComplexUnitCharge.ext
  funext A
  apply tsum_congr
  rintro ⟨side,p | (⟨i,bit⟩ | u)⟩
  · rfl
  · by_cases hi : i < a
    · simp only [indexedAtomCharge, complexHistoryFamilyCharge, dif_pos hi, complexFinalFamilyCharge]
    · have hz := hsupport side bit i (le_of_not_gt hi)
      change c (familyAtom side bit i) * _ = c (familyAtom side bit i) * _
      rw [hz,zero_mul,zero_mul]
  · rfl

def complexCoefficientFactory {μ μt : ConstructionIndex → ComplexAtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (Uinf : Ultrafilter Point)
    (c ct : ConstructionIndex → ComplexFullCoefficientRows)
    (hc : ∀ a n, ‖c a n‖ ≤ 1) (hct : ∀ a n, ‖ct a n‖ ≤ 1)
    (a : ConstructionIndex) (h : ∀ i, i < a → ComplexCodedStage (μ i) (μt i) (R i) (Rt i)) :
    ComplexChargeSequences :=
  (fun n => complexIndexedCodeCharge Uinf (complexHistoryFamilyCharge a h) (c a n) (hc a n),
   fun n => complexIndexedCodeCharge Uinf (complexHistoryFamilyCharge a h) (ct a n) (hct a n))

theorem complexCoefficientFactory_eq_final {μ μt : ConstructionIndex → ComplexAtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (d : ComplexCodedConstruction μ μt R Rt)
    (Uinf : Ultrafilter Point) (c ct : ConstructionIndex → ComplexFullCoefficientRows)
    (hc : ∀ a n, ‖c a n‖ ≤ 1) (hct : ∀ a n, ‖ct a n‖ ≤ 1)
    (hs : ∀ a n side bit i, a ≤ i → c a n (familyAtom side bit i) = 0)
    (hst : ∀ a n side bit i, a ≤ i → ct a n (familyAtom side bit i) = 0) (a : ConstructionIndex) :
    complexCoefficientFactory Uinf c ct hc hct a (fun i _ => d i) =
      (fun n => complexIndexedCodeCharge Uinf (complexFinalFamilyCharge d) (c a n) (hc a n),
       fun n => complexIndexedCodeCharge Uinf (complexFinalFamilyCharge d) (ct a n) (hct a n)) := by
  apply Prod.ext
  · funext n
    exact complexHistoryCodeCharge_eq_final d a Uinf (c a n) (hc a n) (hs a n)
  · funext n
    exact complexHistoryCodeCharge_eq_final d a Uinf (ct a n) (hct a n) (hst a n)

end SigmaNonprimarity


