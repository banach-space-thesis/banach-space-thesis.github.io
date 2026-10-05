import Sigma.TransfiniteConstruction
import ThesisCommon.Analysis.CountableCoefficientCodes
import ThesisCommon.Analysis.LpOneRestriction

/-! Universal coefficient sequences, including an infinity coordinate in each
copy. Family coefficients at and beyond a stage are set to zero. Repetition
cofinally often proves that every original code occurs unchanged. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

abbrev FullAtom := Bool × (Point ⊕ ((ConstructionIndex × Bool) ⊕ Unit))
abbrev FullCoefficientRows := ℕ → lp (fun _ : FullAtom => ℝ) 1

def familyAtom (side bit : Bool) (i : ConstructionIndex) : FullAtom :=
  (side,Sum.inr (Sum.inl (i,bit)))

theorem familyAtom_injective (side bit : Bool) : Function.Injective (familyAtom side bit) := by
  intro i j h
  simpa only [familyAtom, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq, true_and, and_true] using h

theorem fullAtom_cardinal_le : #FullAtom ≤ 𝔠 := by
  have hsum {α β : Type} (hα : #α ≤ 𝔠) (hβ : #β ≤ 𝔠) : #(α ⊕ β) ≤ 𝔠 := by
    simpa only [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.continuum_add_self] using add_le_add hα hβ
  have hprod {α β : Type} (hα : #α ≤ 𝔠) (hβ : #β ≤ 𝔠) : #(α × β) ≤ 𝔠 := by
    simpa only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.continuum_mul_self] using mul_le_mul' hα hβ
  have hb : #Bool ≤ 𝔠 := Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
  have hu : #Unit ≤ 𝔠 := Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
  have hn : #ℕ ≤ 𝔠 := Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
  exact hprod hb (hsum (hprod hn hb) (hsum (hprod constructionIndex_cardinal.le hb) hu))

theorem fullCoefficientRows_cardinal_le : #FullCoefficientRows ≤ 𝔠 := by
  haveI : Nonempty FullAtom := ⟨(false,Sum.inl (0,false))⟩
  have h := lp_one_cardinal_le_continuum fullAtom_cardinal_le
  have hpow : #(lp (fun _ : FullAtom => ℝ) 1) ^ ℵ₀ ≤ 𝔠 ^ ℵ₀ :=
    Cardinal.power_le_power_right h
  simpa only [FullCoefficientRows, Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.continuum_power_aleph0] using hpow

def familySupport (c : FullCoefficientRows) : Set ConstructionIndex :=
  ⋃ n : ℕ, ⋃ side : Bool, ⋃ bit : Bool, (familyAtom side bit) ⁻¹' Function.support (c n)

theorem familySupport_countable (c : FullCoefficientRows) : (familySupport c).Countable :=
  Set.countable_iUnion (fun n => Set.countable_iUnion (fun side => Set.countable_iUnion (fun bit =>
    (lp_one_countable_support (c n)).preimage (familyAtom_injective side bit))))

theorem familySupport_bounded (c : FullCoefficientRows) :
    ∃ a : ConstructionIndex, ∀ n side bit i, c n (familyAtom side bit i) ≠ 0 → i < a := by
  obtain ⟨a,ha⟩ := countable_below_continuum_stage (familySupport_countable c)
  exact ⟨a,fun n side bit i hi => ha i (Set.mem_iUnion.mpr ⟨n,
    Set.mem_iUnion.mpr ⟨side,Set.mem_iUnion.mpr ⟨bit,hi⟩⟩⟩)⟩

def atomsBefore (a : ConstructionIndex) : Set FullAtom :=
  {p | match p.2 with
    | .inl _ => True
    | .inr (.inl q) => q.1 < a
    | .inr (.inr _) => True}

def truncateCoefficients (a : ConstructionIndex) (c : FullCoefficientRows) : FullCoefficientRows :=
  fun n => lpOneRestrict (atomsBefore a) (c n)

theorem truncateCoefficients_norm_le (a : ConstructionIndex) (c : FullCoefficientRows) (n : ℕ) :
    ‖truncateCoefficients a c n‖ ≤ ‖c n‖ := lpOneRestrict_norm_le _ _

theorem truncateCoefficients_base (a : ConstructionIndex) (c : FullCoefficientRows)
    (n : ℕ) (side : Bool) (p : Point) :
    truncateCoefficients a c n (side,Sum.inl p) = c n (side,Sum.inl p) := by
  rw [truncateCoefficients,lpOneRestrict_apply,if_pos (show (side,Sum.inl p) ∈ atomsBefore a from trivial)]

theorem truncateCoefficients_infinity (a : ConstructionIndex) (c : FullCoefficientRows)
    (n : ℕ) (side : Bool) :
    truncateCoefficients a c n (side,Sum.inr (Sum.inr ())) = c n (side,Sum.inr (Sum.inr ())) := by
  rw [truncateCoefficients,lpOneRestrict_apply,
    if_pos (show (side,Sum.inr (Sum.inr ())) ∈ atomsBefore a from trivial)]

theorem truncateCoefficients_future (a : ConstructionIndex) (c : FullCoefficientRows)
    (n : ℕ) (side bit : Bool) (i : ConstructionIndex) (hi : a ≤ i) :
    truncateCoefficients a c n (familyAtom side bit i) = 0 := by
  rw [truncateCoefficients,lpOneRestrict_apply]
  exact if_neg (not_lt.mpr hi)

theorem truncateCoefficients_eq_self (a : ConstructionIndex) (c : FullCoefficientRows)
    (h : ∀ n side bit i, c n (familyAtom side bit i) ≠ 0 → i < a) :
    truncateCoefficients a c = c := by
  funext n
  apply lpOneRestrict_eq_self
  rintro ⟨side,p | (⟨i,bit⟩ | u)⟩ hp
  · trivial
  · exact h n side bit i hp
  · trivial

/-- A full enumeration with the support-before-stage condition. The hypotheses
on a chosen class only require closure under the explicit truncation. -/
theorem exists_supported_coefficient_enumeration
    (P : FullCoefficientRows → Prop) (hne : ∃ c, P c)
    (htruncate : ∀ a c, P c → P (truncateCoefficients a c)) :
    ∃ e : ConstructionIndex → FullCoefficientRows,
      (∀ a, P (e a)) ∧
      (∀ a n side bit i, a ≤ i → e a n (familyAtom side bit i) = 0) ∧
      ∀ c, P c → ∃ a, e a = c := by
  classical
  haveI : Nonempty {c // P c} := hne.elim (fun c hc => ⟨⟨c,hc⟩⟩)
  have hcard : #{c // P c} ≤ 𝔠 := Cardinal.mk_subtype_le _ |>.trans fullCoefficientRows_cardinal_le
  obtain ⟨s,hs⟩ := exists_cofinal_schedule constructionIndex_cardinal
    Cardinal.mk_Iio_ord_toType hcard
  refine ⟨fun a => truncateCoefficients a (s a).val,
    fun a => htruncate a _ (s a).property,
    fun a n side bit i hi => truncateCoefficients_future a _ n side bit i hi, ?_⟩
  intro c hc
  obtain ⟨bound,hbound⟩ := familySupport_bounded c
  obtain ⟨a,ha,hea⟩ := hs ⟨c,hc⟩ bound
  refine ⟨a,?_⟩
  change truncateCoefficients a (s a).val = c
  rw [hea]
  exact truncateCoefficients_eq_self a c (fun n side bit i hi => (hbound n side bit i hi).trans_le ha)

end SigmaNonprimarity
