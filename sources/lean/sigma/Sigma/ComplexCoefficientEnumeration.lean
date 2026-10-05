import Sigma.CoefficientEnumeration
import ThesisCommon.Analysis.SigmaComplexCoefficientCodes
import JLMS.L1Restriction

/-! Universal coefficient sequences, including an infinity coordinate in each
copy. Family coefficients at and beyond a stage are set to zero. Repetition
cofinally often proves that every original code occurs unchanged. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

abbrev ComplexFullCoefficientRows := ℕ → lp (fun _ : FullAtom => ℂ) 1

theorem complexLpOneRestrict_eq_self {ι : Type*} (S : Set ι) (f : lp (fun _ : ι => ℂ) 1)
    (hf : Function.support f ⊆ S) : JLMS.restrictL1 S f = f := by
  classical
  apply lp.ext
  funext i
  rw [JLMS.restrictL1_apply]
  by_cases hi : i ∈ S
  · exact if_pos hi
  · rw [if_neg hi]
    by_contra h
    exact hi (hf (Ne.symm h))

theorem complexFullCoefficientRows_cardinal_le : #ComplexFullCoefficientRows ≤ 𝔠 := by
  haveI : Nonempty FullAtom := ⟨(false,Sum.inl (0,false))⟩
  have h := complex_lp_one_cardinal_le_continuum fullAtom_cardinal_le
  have hpow : #(lp (fun _ : FullAtom => ℂ) 1) ^ ℵ₀ ≤ 𝔠 ^ ℵ₀ :=
    Cardinal.power_le_power_right h
  simpa only [ComplexFullCoefficientRows, Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.continuum_power_aleph0] using hpow

def complexFamilySupport (c : ComplexFullCoefficientRows) : Set ConstructionIndex :=
  ⋃ n : ℕ, ⋃ side : Bool, ⋃ bit : Bool, (familyAtom side bit) ⁻¹' Function.support (c n)

theorem complexFamilySupport_countable (c : ComplexFullCoefficientRows) : (complexFamilySupport c).Countable :=
  Set.countable_iUnion (fun n => Set.countable_iUnion (fun side => Set.countable_iUnion (fun bit =>
    (complex_lp_one_countable_support (c n)).preimage (familyAtom_injective side bit))))

theorem complexFamilySupport_bounded (c : ComplexFullCoefficientRows) :
    ∃ a : ConstructionIndex, ∀ n side bit i, c n (familyAtom side bit i) ≠ 0 → i < a := by
  obtain ⟨a,ha⟩ := countable_below_continuum_stage (complexFamilySupport_countable c)
  exact ⟨a,fun n side bit i hi => ha i (Set.mem_iUnion.mpr ⟨n,
    Set.mem_iUnion.mpr ⟨side,Set.mem_iUnion.mpr ⟨bit,hi⟩⟩⟩)⟩

def complexTruncateCoefficients (a : ConstructionIndex) (c : ComplexFullCoefficientRows) : ComplexFullCoefficientRows :=
  fun n => JLMS.restrictL1 (atomsBefore a) (c n)

theorem complexTruncateCoefficients_norm_le (a : ConstructionIndex) (c : ComplexFullCoefficientRows) (n : ℕ) :
    ‖complexTruncateCoefficients a c n‖ ≤ ‖c n‖ := JLMS.restrictL1_norm_le _ _

theorem complexTruncateCoefficients_base (a : ConstructionIndex) (c : ComplexFullCoefficientRows)
    (n : ℕ) (side : Bool) (p : Point) :
    complexTruncateCoefficients a c n (side,Sum.inl p) = c n (side,Sum.inl p) := by
  rw [complexTruncateCoefficients,JLMS.restrictL1_apply,if_pos (show (side,Sum.inl p) ∈ atomsBefore a from trivial)]

theorem complexTruncateCoefficients_infinity (a : ConstructionIndex) (c : ComplexFullCoefficientRows)
    (n : ℕ) (side : Bool) :
    complexTruncateCoefficients a c n (side,Sum.inr (Sum.inr ())) = c n (side,Sum.inr (Sum.inr ())) := by
  rw [complexTruncateCoefficients,JLMS.restrictL1_apply,
    if_pos (show (side,Sum.inr (Sum.inr ())) ∈ atomsBefore a from trivial)]

theorem complexTruncateCoefficients_future (a : ConstructionIndex) (c : ComplexFullCoefficientRows)
    (n : ℕ) (side bit : Bool) (i : ConstructionIndex) (hi : a ≤ i) :
    complexTruncateCoefficients a c n (familyAtom side bit i) = 0 := by
  rw [complexTruncateCoefficients,JLMS.restrictL1_apply]
  exact if_neg (not_lt.mpr hi)

theorem complexTruncateCoefficients_eq_self (a : ConstructionIndex) (c : ComplexFullCoefficientRows)
    (h : ∀ n side bit i, c n (familyAtom side bit i) ≠ 0 → i < a) :
    complexTruncateCoefficients a c = c := by
  funext n
  apply complexLpOneRestrict_eq_self
  rintro ⟨side,p | (⟨i,bit⟩ | u)⟩ hp
  · trivial
  · exact h n side bit i hp
  · trivial

/-- A full enumeration with the support-before-stage condition. The hypotheses
on a chosen class only require closure under the explicit truncation. -/
theorem complex_exists_supported_coefficient_enumeration
    (P : ComplexFullCoefficientRows → Prop) (hne : ∃ c, P c)
    (htruncate : ∀ a c, P c → P (complexTruncateCoefficients a c)) :
    ∃ e : ConstructionIndex → ComplexFullCoefficientRows,
      (∀ a, P (e a)) ∧
      (∀ a n side bit i, a ≤ i → e a n (familyAtom side bit i) = 0) ∧
      ∀ c, P c → ∃ a, e a = c := by
  classical
  haveI : Nonempty {c // P c} := hne.elim (fun c hc => ⟨⟨c,hc⟩⟩)
  have hcard : #{c // P c} ≤ 𝔠 := Cardinal.mk_subtype_le _ |>.trans complexFullCoefficientRows_cardinal_le
  obtain ⟨s,hs⟩ := exists_cofinal_schedule constructionIndex_cardinal
    Cardinal.mk_Iio_ord_toType hcard
  refine ⟨fun a => complexTruncateCoefficients a (s a).val,
    fun a => htruncate a _ (s a).property,
    fun a n side bit i hi => complexTruncateCoefficients_future a _ n side bit i hi, ?_⟩
  intro c hc
  obtain ⟨bound,hbound⟩ := complexFamilySupport_bounded c
  obtain ⟨a,ha,hea⟩ := hs ⟨c,hc⟩ bound
  refine ⟨a,?_⟩
  change complexTruncateCoefficients a (s a).val = c
  rw [hea]
  exact complexTruncateCoefficients_eq_self a c (fun n side bit i hi => (hbound n side bit i hi).trans_le ha)

end SigmaNonprimarity
