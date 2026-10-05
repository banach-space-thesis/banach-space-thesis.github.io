import ThesisCommon.Analysis.L1BandCoding

/-! The singular and band-projection parts of Lemma 4.3 for the actual
coding isometries used in the countably generated standard-space reduction.
Arbitrary measure-algebra isomorphisms are a separate extension. -/
noncomputable section
open MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y A B : Type*}
variable [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable [mA : MeasurableSpace A] [mB : MeasurableSpace B]
variable (μ : Measure X) (ν : Measure Y)
variable (a : X → A) (ha : Measurable a) (hagen : mA.comap a = mX)
variable (b : Y → B) (hb : Measurable b) (hbgen : mB.comap b = mY)

theorem lemma_4_3_coding_singular_step [SFinite (μ.map a)]
    (S : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    IsSingularOperator (lpTransportOperator μ ν a ha hagen b hb hbgen S) ↔ IsSingularOperator S :=
  isSingularOperator_lpTransport_iff μ ν a ha hagen b hb hbgen S

theorem lemma_4_3_coding_lattice_step (S T : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    lpTransportOperator μ ν a ha hagen b hb hbgen (S ⊓ T) =
      lpTransportOperator μ ν a ha hagen b hb hbgen S ⊓ lpTransportOperator μ ν a ha hagen b hb hbgen T :=
  lpTransportOperator_inf μ ν a ha hagen b hb hbgen S T

theorem lemma_4_3_coding_band_projection_step [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (T : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    integralBandProjection (lpTransportOperator μ ν a ha hagen b hb hbgen T) =
      lpTransportOperator μ ν a ha hagen b hb hbgen (integralBandProjection T) :=
  integralBandProjection_lpTransport μ ν a ha hagen b hb hbgen T

end PEMS
