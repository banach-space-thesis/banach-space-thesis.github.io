import Sigma.ComplexHistoryCharges
import Sigma.ComplexConstructedFamilies

/-! An unconditional construction for all admissible coefficient codes. The
existence theorem below constructs every field; no construction invariant is
assumed. The remaining analytic bridge is from actual norming sequences to
these indexed coefficients and their final JL evaluations. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity

structure ComplexEnumeratedConstruction where
  reserve : Set ℕ
  reserve_infinite : reserve.Infinite
  complement_infinite : reserveᶜ.Infinite
  stock : ConstructionIndex → Set ℕ
  stock_inside : ∀ i, stock i ⊆ reserve
  stock_infinite : ∀ i, (stock i).Infinite
  stock_pairwise : Pairwise (fun i j => (stock i ∩ stock j).Finite)
  leftCode : ConstructionIndex → ComplexFullCoefficientRows
  rightCode : ConstructionIndex → ComplexFullCoefficientRows
  left_admissible : ∀ a, ComplexFullCodeAdmissible false (leftCode a)
  right_admissible : ∀ a, ComplexFullCodeAdmissible true (rightCode a)
  left_supported : ∀ a n side bit i, a ≤ i → leftCode a n (familyAtom side bit i) = 0
  right_supported : ∀ a n side bit i, a ≤ i → rightCode a n (familyAtom side bit i) = 0
  left_covers : ∀ c, ComplexFullCodeAdmissible false c → ∃ a, leftCode a = c
  right_covers : ∀ c, ComplexFullCodeAdmissible true c → ∃ a, rightCode a = c
  data : ComplexCodedConstruction (fun a => complexCodeAtomicRows false (leftCode a))
    (fun a => complexCodeAtomicRows true (rightCode a)) stock stock
  good : data.Good Set.univ
  charge_agreement : ∀ a, (data a).measures =
    (fun n => complexIndexedCodeCharge (reservedInfinityUltrafilter reserve complement_infinite)
      (complexFinalFamilyCharge data) (leftCode a n) ((left_admissible a).1 n),
     fun n => complexIndexedCodeCharge (reservedInfinityUltrafilter reserve complement_infinite)
      (complexFinalFamilyCharge data) (rightCode a n) ((right_admissible a).1 n))

theorem complex_exists_enumeratedConstruction : Nonempty ComplexEnumeratedConstruction := by
  obtain ⟨C,R,hC,hCc,hR,hpair⟩ := exists_reserved_stock
  obtain ⟨c,hc,hcs,hcover⟩ := complex_exists_admissible_code_enumeration false
  obtain ⟨ct,hct,hcts,hcovert⟩ := complex_exists_admissible_code_enumeration true
  let μ : ConstructionIndex → ComplexAtomicRows := fun a => complexCodeAtomicRows false (c a)
  let μt : ConstructionIndex → ComplexAtomicRows := fun a => complexCodeAtomicRows true (ct a)
  let Uinf := reservedInfinityUltrafilter C hCc
  obtain ⟨d,hgood,_,hfactory⟩ := complex_exists_adaptive_continuum_construction μ μt R R
    (complexCoefficientFactory Uinf c ct (fun a => (hc a).1) (fun a => (hct a).1))
    (fun a => complexCodeAtomicRows_admissible false (c a) (hc a))
    (fun a => complexCodeAtomicRows_admissible true (ct a) (hct a))
    (fun a => (hR a).2) (fun a => (hR a).2)
  refine ⟨{
    reserve := C
    reserve_infinite := hC
    complement_infinite := hCc
    stock := R
    stock_inside := fun i => (hR i).1
    stock_infinite := fun i => (hR i).2
    stock_pairwise := hpair
    leftCode := c
    rightCode := ct
    left_admissible := hc
    right_admissible := hct
    left_supported := hcs
    right_supported := hcts
    left_covers := hcover
    right_covers := hcovert
    data := d
    good := hgood
    charge_agreement := ?_ }⟩
  intro a
  exact (hfactory a).trans
    (complexCoefficientFactory_eq_final d Uinf c ct (fun a => (hc a).1) (fun a => (hct a).1) hcs hcts a)

theorem ComplexEnumeratedConstruction.family_properties (D : ComplexEnumeratedConstruction) :
    (AlmostDisjoint (splitFamily (fun i => (D.data i).choices.1.J₁)
      (fun i => (D.data i).choices.1.Z)) ∧
      (splitFamily (fun i => (D.data i).choices.1.J₁) (fun i => (D.data i).choices.1.Z)).Infinite) ∧
    (AlmostDisjoint (splitFamily (fun i => (D.data i).choices.2.J₁)
      (fun i => (D.data i).choices.2.Z)) ∧
      (splitFamily (fun i => (D.data i).choices.2.J₁) (fun i => (D.data i).choices.2.Z)).Infinite) := by
  haveI : Infinite ConstructionIndex := Cardinal.infinite_iff.mpr (by
    rw [constructionIndex_cardinal]
    exact Cardinal.aleph0_le_continuum)
  exact ⟨complex_threeLevelChoice_family_properties _ _ (fun i => (D.data i).choices.1) D.stock_pairwise,
    complex_threeLevelChoice_family_properties _ _ (fun i => (D.data i).choices.2) D.stock_pairwise⟩

end SigmaNonprimarity


