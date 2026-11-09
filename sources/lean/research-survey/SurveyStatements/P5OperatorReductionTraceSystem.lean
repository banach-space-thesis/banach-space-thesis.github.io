import SurveyStatements.P5OperatorReductionTraceNormalization
import SurveyStatements.P5OperatorReductionOuterSlices
import SurveyStatements.P5OperatorReductionOuterShadowTraceValues

/-! Both normalized trace families are fixed from the actual mixed
operator before constructing its alternating faithful block histories. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open Filter
open scoped ENNReal Classical Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
open SurveyStatements.P5L1Variation
variable {𝕜 : Type*} [RCLike 𝕜]

def splitRawWeight (S : LpHaarFiniteSplit) : ℝ → 𝕜 :=
  operatorReductionRawPacketFunction S.level S.atoms (fun k => scalarSign (S.signs k))

theorem splitRawWeight_measurable (S : LpHaarFiniteSplit) :
    StronglyMeasurable (splitRawWeight (𝕜 := 𝕜) S) :=
  rawPacketFunction_stronglyMeasurable S.level S.atoms _

theorem splitRawWeight_bound (S : LpHaarFiniteSplit) :
    ∀ x, ‖splitRawWeight (𝕜 := 𝕜) S x‖ ≤ 1 :=
  norm_rawPacketFunction_le_one S.level S.atoms _
    (fun k _ => (norm_scalarSign_eq_one (𝕜 := 𝕜) (S.signs k)).le)

abbrev UniversalInnerPairRegisteredTraces (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) (r : ℕ → ℕ) :=
  ∀ pair : LpHaarFiniteSplit × LpHaarFiniteSplit,
    RegisteredDyadicTrace
      (fun n k => lpHaarDyadicCoefficient 𝕜 p n k
        (innerPairOuterSlice p T pair (lpHaarDyadic 𝕜 p n k)))
      r (6 * ‖innerPairOuterSlice p T pair‖)

def actualNormalizedOuterTrace (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) {r : ℕ → ℕ}
    (a : UniversalInnerPairRegisteredTraces p T r) : NormalizedBlockTrace 𝕜 :=
  normalizedRegisteredBlockTrace a

def actualNormalizedInnerTrace (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) : NormalizedBlockTrace 𝕜 :=
  fun pair P => (unitIntervalMeasure.real pair.1.parent.set : 𝕜)⁻¹ *
    normalizedParentTrace
      (innerSliceDyadicTraceValue p T (pair.2.vector 𝕜 p) (splitRawWeight pair.1)
        (splitRawWeight_measurable pair.1) (splitRawWeight_bound pair.1)) P

def actualInnerSliceRegisteredTrace (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val unitIntervalMeasure)
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1) :
    RegisteredDyadicTrace
      (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 (meanZeroInnerSlice T f η hη hb)))
      id (‖T‖ * ‖f‖) where
  value := innerSliceDyadicTraceValue p T f η hη hb
  bound := norm_innerSliceDyadicTraceValue_le p T f η hη hb
  limit := innerSliceDyadicTraceValue_full_tendsto p T f η hη hb
  equal_sets := innerSliceDyadicTraceValue_equal_sets p T f η hη hb
  additive := innerSliceDyadicTraceValue_additive p T f η hη hb

theorem actualNormalizedOuterTrace_equal_sets (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) {r : ℕ → ℕ}
    (a : UniversalInnerPairRegisteredTraces p T r)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit)
    (P Q : LpHaarFiniteParent) (hPQ : P.set = Q.set) :
    actualNormalizedOuterTrace p T a pair P = actualNormalizedOuterTrace p T a pair Q :=
  normalizedRegisteredBlockTrace_equal_sets a pair P Q hPQ

theorem actualNormalizedInnerTrace_equal_sets (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit)
    (P Q : LpHaarFiniteParent) (hPQ : P.set = Q.set) :
    actualNormalizedInnerTrace p T pair P = actualNormalizedInnerTrace p T pair Q := by
  apply congrArg (fun z : 𝕜 => (unitIntervalMeasure.real pair.1.parent.set : 𝕜)⁻¹ * z)
  exact normalizedParentTrace_equal_sets _
    (innerSliceDyadicTraceValue_equal_sets p T (pair.2.vector 𝕜 p) (splitRawWeight pair.1)
      (splitRawWeight_measurable pair.1) (splitRawWeight_bound pair.1)) P Q hPQ

theorem actualNormalizedInnerTrace_eq_local (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    actualNormalizedInnerTrace p T pair P =
      (unitIntervalMeasure.real pair.1.parent.set : 𝕜)⁻¹ *
        localTraceFunctional 𝕜 P.level P.atoms
          (meanZeroInnerSlice T (pair.2.vector 𝕜 p) (splitRawWeight pair.1)
            (splitRawWeight_measurable pair.1) (splitRawWeight_bound pair.1)) := by
  have hm : (unitIntervalMeasure.real P.set : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr P.mass_pos.ne'
  unfold actualNormalizedInnerTrace
  apply congrArg (fun z : 𝕜 => (unitIntervalMeasure.real pair.1.parent.set : 𝕜)⁻¹ * z)
  unfold normalizedParentTrace innerSliceDyadicTraceValue
  change (unitIntervalMeasure.real P.set : 𝕜)⁻¹ *
    ((unitIntervalMeasure.real P.set : 𝕜) * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]

theorem norm_actualNormalizedOuterTrace_le (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) {r : ℕ → ℕ}
    (a : UniversalInnerPairRegisteredTraces p T r)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    ‖actualNormalizedOuterTrace p T a pair P‖ ≤ 6 * ‖innerPairOuterSlice p T pair‖ := by
  have hm : 0 < unitIntervalMeasure.real P.set := P.mass_pos
  change ‖(unitIntervalMeasure.real P.set : 𝕜)⁻¹ *
    (a pair).value ⟨P.level, P.atoms⟩‖ ≤ _
  rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hm]
  apply (mul_le_mul_of_nonneg_left ((a pair).bound ⟨P.level, P.atoms⟩)
    (inv_nonneg.mpr hm.le)).trans_eq
  change (unitIntervalMeasure.real P.set)⁻¹ *
    ((6 * ‖innerPairOuterSlice p T pair‖) * unitIntervalMeasure.real P.set) = _
  field_simp [hm.ne']

theorem norm_actualNormalizedInnerTrace_le (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    ‖actualNormalizedInnerTrace p T pair P‖ ≤
      (unitIntervalMeasure.real pair.1.parent.set)⁻¹ *
        (‖T‖ * ‖pair.2.vector 𝕜 p‖) := by
  have hparent : 0 < unitIntervalMeasure.real pair.1.parent.set := pair.1.parent.mass_pos
  rw [actualNormalizedInnerTrace_eq_local, norm_mul, norm_inv, RCLike.norm_ofReal,
    abs_of_pos hparent]
  exact mul_le_mul_of_nonneg_left
    (norm_innerSliceLocalTrace_le p T (pair.2.vector 𝕜 p) (splitRawWeight pair.1)
      (splitRawWeight_measurable pair.1) (splitRawWeight_bound pair.1) P.level P.atoms)
    (inv_nonneg.mpr hparent.le)

end SurveyStatements.P5OperatorReduction
