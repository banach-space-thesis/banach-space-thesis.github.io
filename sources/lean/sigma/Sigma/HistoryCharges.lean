import Sigma.CodeAtomicRows
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

def ThreeLevelChoice.piece {μ : AtomicRows} {R : Set ℕ} (d : ThreeLevelChoice μ R) : Bool → Set Point
  | false => d.Z
  | true => cylinder d.J₁ \ d.Z

theorem ThreeLevelChoice.piece_infinite {μ : AtomicRows} {R : Set ℕ}
    (d : ThreeLevelChoice μ R) (bit : Bool) : (d.piece bit).Infinite := by
  have hJ := d.infinite_J₂.mono d.J₂_subset
  cases bit
  · exact d.splits.infinite hJ
  · exact d.splits.other.infinite hJ

def ThreeLevelChoice.pieceCharge {μ : AtomicRows} {R : Set ℕ}
    (d : ThreeLevelChoice μ R) (bit : Bool) : UnitCharge Point :=
  ultrafilterCharge (freeUltrafilterOn (d.piece bit) (d.piece_infinite bit))

def putInCopy (side : Bool) (μ : UnitCharge Point) : PairedMeasure :=
  μ.map (fun p => if side then Sum.inr (pointCode p) else Sum.inl (pointCode p))

def indexedAtomCharge (Uinf : Ultrafilter Point)
    (F : Bool → ConstructionIndex → Bool → UnitCharge Point) : FullAtom → PairedMeasure
  | (side,.inl p) => putInCopy side (diracCharge p)
  | (side,.inr (.inl (i,bit))) => putInCopy side (F side i bit)
  | (side,.inr (.inr _)) => putInCopy side (ultrafilterCharge Uinf)

def historyFamilyCharge {μ μt : ConstructionIndex → AtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (a : ConstructionIndex)
    (h : ∀ i, i < a → CodedStage (μ i) (μt i) (R i) (Rt i))
    (side : Bool) (i : ConstructionIndex) (bit : Bool) : UnitCharge Point :=
  if hi : i < a then
    if side then (h i hi).choices.2.pieceCharge bit else (h i hi).choices.1.pieceCharge bit
  else 0

def finalFamilyCharge {μ μt : ConstructionIndex → AtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (d : CodedConstruction μ μt R Rt)
    (side : Bool) (i : ConstructionIndex) (bit : Bool) : UnitCharge Point :=
  if side then (d i).choices.2.pieceCharge bit else (d i).choices.1.pieceCharge bit

def indexedCodeCharge (Uinf : Ultrafilter Point)
    (F : Bool → ConstructionIndex → Bool → UnitCharge Point)
    (c : lp (fun _ : FullAtom => ℝ) 1) (hc : ‖c‖ ≤ 1) : PairedMeasure :=
  lpChargeSeries c hc (indexedAtomCharge Uinf F)

theorem historyCodeCharge_eq_final {μ μt : ConstructionIndex → AtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (d : CodedConstruction μ μt R Rt)
    (a : ConstructionIndex) (Uinf : Ultrafilter Point)
    (c : lp (fun _ : FullAtom => ℝ) 1) (hc : ‖c‖ ≤ 1)
    (hsupport : ∀ side bit i, a ≤ i → c (familyAtom side bit i) = 0) :
    indexedCodeCharge Uinf (historyFamilyCharge a (fun i _ => d i)) c hc =
      indexedCodeCharge Uinf (finalFamilyCharge d) c hc := by
  apply UnitCharge.ext
  funext A
  apply tsum_congr
  rintro ⟨side,p | (⟨i,bit⟩ | u)⟩
  · rfl
  · by_cases hi : i < a
    · simp only [indexedAtomCharge, historyFamilyCharge, dif_pos hi, finalFamilyCharge]
    · have hz := hsupport side bit i (le_of_not_gt hi)
      change c (familyAtom side bit i) * _ = c (familyAtom side bit i) * _
      rw [hz,zero_mul,zero_mul]
  · rfl

def coefficientFactory {μ μt : ConstructionIndex → AtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (Uinf : Ultrafilter Point)
    (c ct : ConstructionIndex → FullCoefficientRows)
    (hc : ∀ a n, ‖c a n‖ ≤ 1) (hct : ∀ a n, ‖ct a n‖ ≤ 1)
    (a : ConstructionIndex) (h : ∀ i, i < a → CodedStage (μ i) (μt i) (R i) (Rt i)) :
    ChargeSequences :=
  (fun n => indexedCodeCharge Uinf (historyFamilyCharge a h) (c a n) (hc a n),
   fun n => indexedCodeCharge Uinf (historyFamilyCharge a h) (ct a n) (hct a n))

theorem coefficientFactory_eq_final {μ μt : ConstructionIndex → AtomicRows}
    {R Rt : ConstructionIndex → Set ℕ} (d : CodedConstruction μ μt R Rt)
    (Uinf : Ultrafilter Point) (c ct : ConstructionIndex → FullCoefficientRows)
    (hc : ∀ a n, ‖c a n‖ ≤ 1) (hct : ∀ a n, ‖ct a n‖ ≤ 1)
    (hs : ∀ a n side bit i, a ≤ i → c a n (familyAtom side bit i) = 0)
    (hst : ∀ a n side bit i, a ≤ i → ct a n (familyAtom side bit i) = 0) (a : ConstructionIndex) :
    coefficientFactory Uinf c ct hc hct a (fun i _ => d i) =
      (fun n => indexedCodeCharge Uinf (finalFamilyCharge d) (c a n) (hc a n),
       fun n => indexedCodeCharge Uinf (finalFamilyCharge d) (ct a n) (hct a n)) := by
  apply Prod.ext
  · funext n
    exact historyCodeCharge_eq_final d a Uinf (c a n) (hc a n) (hs a n)
  · funext n
    exact historyCodeCharge_eq_final d a Uinf (ct a n) (hct a n) (hst a n)

end SigmaNonprimarity
