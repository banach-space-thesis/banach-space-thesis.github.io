import ThesisCommon.Analysis.ALCountableSup
import ThesisCommon.Analysis.L1OperatorModulus
import ThesisCommon.Analysis.L1ModulusCoding

/-! The real order-theoretic background in PEMS Section 3. Proposition 3.1
is proved in its stated sigma-finite form; the shared result needs no measure
restriction. The modulus and regularity results concern actual real L¹ spaces.
Complexification and the absolute-kernel theorem are separate obligations. -/
noncomputable section
open Set MeasureTheory ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Proposition 3.1 (prop: countable-supremum-property): every subset of a
sigma-finite real L¹ space having a supremum has a countable subset with the
same supremum. IsLUB expresses the supremum without an arbitrary default. -/
def Proposition_3_1 (μ : Measure X) [SigmaFinite μ] : Prop :=
  ∀ (s : Set (Lp ℝ 1 μ)) (z : Lp ℝ 1 μ), IsLUB s z →
    ∃ c : Set (Lp ℝ 1 μ), c ⊆ s ∧ c.Countable ∧ IsLUB c z

theorem proposition_3_1_proof (μ : Measure X) [SigmaFinite μ] : Proposition_3_1 μ :=
  fun _ _ hz => al_countable_sup_property (lOne_norm_add_of_nonneg μ) hz

/-- The real L¹ instance of eq: reg-equal-bounded, in the direction needed
by the kernel argument: every bounded operator is a difference of positives. -/
theorem real_lOne_operator_regular (μ : Measure X) (ν : Measure Y)
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃ P Q : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, (∀ f, 0 ≤ f → 0 ≤ P f) ∧
      (∀ f, 0 ≤ f → 0 ≤ Q f) ∧ T = P - Q := lOne_operator_regular T

/-- First equality of eq: modulus-and-norm-relation. Adjoint commutation is
not asserted here and remains a separate proof obligation. -/
theorem real_lOne_norm_modulus (μ : Measure X) (ν : Measure Y)
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : ‖lOneOperatorModulus T‖ = ‖T‖ :=
  norm_lOneOperatorModulus T

/-- The order-interval formula eq: Riesz-Kantorovich, for real L¹ operators. -/
theorem real_lOne_rieszKantorovich (μ : Measure X) (ν : Measure Y)
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    IsLUB (T '' Icc (-f) f) (lOneOperatorModulus T f) :=
  lOneOperatorModulus_rieszKantorovich T f hf

/-- The real operator-modulus step in Lemma 4.3 for the coding isometries
actually used by the standard-space reduction. Band preservation is separate. -/
theorem lemma_4_3_coding_modulus_step {A B : Type*}
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure X) (ν : Measure Y)
    (a : X → A) (ha : Measurable a) (hagen : mA.comap a = ‹MeasurableSpace X›)
    (b : Y → B) (hb : Measurable b) (hbgen : mB.comap b = ‹MeasurableSpace Y›)
    (T : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    lOneOperatorModulus (lpTransportOperator μ ν a ha hagen b hb hbgen T) =
      lpTransportOperator μ ν a ha hagen b hb hbgen (lOneOperatorModulus T) :=
  lOneOperatorModulus_lpTransport μ ν a ha hagen b hb hbgen T

end PEMS
