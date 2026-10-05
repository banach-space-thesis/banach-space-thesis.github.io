import Sigma.HistoryCharges

/-! An unconditional construction for all admissible coefficient codes. The
existence theorem below constructs every field; no construction invariant is
assumed. The remaining analytic bridge is from actual norming sequences to
these indexed coefficients and their final JL evaluations. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity

structure EnumeratedConstruction where
  reserve : Set ℕ
  reserve_infinite : reserve.Infinite
  complement_infinite : reserveᶜ.Infinite
  stock : ConstructionIndex → Set ℕ
  stock_inside : ∀ i, stock i ⊆ reserve
  stock_infinite : ∀ i, (stock i).Infinite
  stock_pairwise : Pairwise (fun i j => (stock i ∩ stock j).Finite)
  leftCode : ConstructionIndex → FullCoefficientRows
  rightCode : ConstructionIndex → FullCoefficientRows
  left_admissible : ∀ a, FullCodeAdmissible false (leftCode a)
  right_admissible : ∀ a, FullCodeAdmissible true (rightCode a)
  left_supported : ∀ a n side bit i, a ≤ i → leftCode a n (familyAtom side bit i) = 0
  right_supported : ∀ a n side bit i, a ≤ i → rightCode a n (familyAtom side bit i) = 0
  left_covers : ∀ c, FullCodeAdmissible false c → ∃ a, leftCode a = c
  right_covers : ∀ c, FullCodeAdmissible true c → ∃ a, rightCode a = c
  data : CodedConstruction (fun a => codeAtomicRows false (leftCode a))
    (fun a => codeAtomicRows true (rightCode a)) stock stock
  good : data.Good Set.univ
  charge_agreement : ∀ a, (data a).measures =
    (fun n => indexedCodeCharge (reservedInfinityUltrafilter reserve complement_infinite)
      (finalFamilyCharge data) (leftCode a n) ((left_admissible a).1 n),
     fun n => indexedCodeCharge (reservedInfinityUltrafilter reserve complement_infinite)
      (finalFamilyCharge data) (rightCode a n) ((right_admissible a).1 n))

theorem exists_enumeratedConstruction : Nonempty EnumeratedConstruction := by
  obtain ⟨C,R,hC,hCc,hR,hpair⟩ := exists_reserved_stock
  obtain ⟨c,hc,hcs,hcover⟩ := exists_admissible_code_enumeration false
  obtain ⟨ct,hct,hcts,hcovert⟩ := exists_admissible_code_enumeration true
  let μ : ConstructionIndex → AtomicRows := fun a => codeAtomicRows false (c a)
  let μt : ConstructionIndex → AtomicRows := fun a => codeAtomicRows true (ct a)
  let Uinf := reservedInfinityUltrafilter C hCc
  obtain ⟨d,hgood,_,hfactory⟩ := exists_adaptive_continuum_construction μ μt R R
    (coefficientFactory Uinf c ct (fun a => (hc a).1) (fun a => (hct a).1))
    (fun a => codeAtomicRows_admissible false (c a) (hc a))
    (fun a => codeAtomicRows_admissible true (ct a) (hct a))
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
    (coefficientFactory_eq_final d Uinf c ct (fun a => (hc a).1) (fun a => (hct a).1) hcs hcts a)

theorem EnumeratedConstruction.family_properties (D : EnumeratedConstruction) :
    (AlmostDisjoint (splitFamily (fun i => (D.data i).choices.1.J₁)
      (fun i => (D.data i).choices.1.Z)) ∧
      (splitFamily (fun i => (D.data i).choices.1.J₁) (fun i => (D.data i).choices.1.Z)).Infinite) ∧
    (AlmostDisjoint (splitFamily (fun i => (D.data i).choices.2.J₁)
      (fun i => (D.data i).choices.2.Z)) ∧
      (splitFamily (fun i => (D.data i).choices.2.J₁) (fun i => (D.data i).choices.2.Z)).Infinite) := by
  haveI : Infinite ConstructionIndex := Cardinal.infinite_iff.mpr (by
    rw [constructionIndex_cardinal]
    exact Cardinal.aleph0_le_continuum)
  exact ⟨threeLevelChoice_family_properties _ _ (fun i => (D.data i).choices.1) D.stock_pairwise,
    threeLevelChoice_family_properties _ _ (fun i => (D.data i).choices.2) D.stock_pairwise⟩

end SigmaNonprimarity
