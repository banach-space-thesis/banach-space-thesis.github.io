import SurveyStatements.P5OperatorReductionTraceSystem
import SurveyStatements.P5OperatorReductionShadowExpansion
import SurveyStatements.P5OperatorReductionBlockReaderWeights
import SurveyStatements.P5OperatorReductionPacketShadowOperators
import SurveyStatements.P5Support.LpHaarTraceSplitSelection

/-! The genuine inner-valued Haar packet shadows have exactly the
registered outer scalar traces after testing against each actual block reader. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 ι : Type*} [RCLike 𝕜]

def rawHaarPacketShadowOperator (p : BanachExponent)
    (n : ι → ℕ) (S : ∀ i, Finset (Fin (2 ^ n i)))
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) (i : ι) :
    Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure :=
  packetShadowOperator (fun i => 2 ^ n i)
    (fun i θ => operatorReductionRawHaarPacket 𝕜 p (n i) (S i)
      (fun k => scalarSign (θ k)))
    (fun i θ => operatorReductionRawPacketFunction (n i) (S i)
      (fun k => scalarSign (θ k)))
    (fun i θ => rawPacketFunction_stronglyMeasurable (n i) (S i) _)
    (fun i θ => norm_rawPacketFunction_le_one (n i) (S i) _
      (fun k _ => (norm_scalarSign_eq_one (𝕜 := 𝕜) (θ k)).le)) T i

theorem rawHaarPacketShadowOperator_apply (p : BanachExponent)
    (n : ι → ℕ) (S : ∀ i, Finset (Fin (2 ^ n i)))
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) (i : ι)
    (g : Lp 𝕜 1 unitIntervalMeasure) :
    rawHaarPacketShadowOperator p n S T i g = rawHaarPacketShadow p n S T g i := by
  exact packetShadowOperator_apply _ _ _ _ _ T i g

theorem norm_rawHaarPacketShadowOperator_le (p : BanachExponent)
    (n : ι → ℕ) (S : ∀ i, Finset (Fin (2 ^ n i)))
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) (i : ι) :
    ‖rawHaarPacketShadowOperator p n S T i‖ ≤ ‖T‖ := by
  apply norm_packetShadowOperator_le
  intro j θ
  filter_upwards [operatorReductionRawHaarPacket_ae (𝕜 := 𝕜) p (n j) (S j)
    (fun k => scalarSign (𝕜 := 𝕜) (θ k))] with x hx
  rw [hx]
  exact norm_rawPacketFunction_le_one (n j) (S j) _
    (fun k _ => (norm_scalarSign_eq_one (𝕜 := 𝕜) (θ k)).le) x

theorem rawHaarPacketShadow_scalar_eq_levelTrace (p : BanachExponent)
    (n : ι → ℕ) (S : ∀ i, Finset (Fin (2 ^ n i)))
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (g : Lp 𝕜 1 unitIntervalMeasure)
    (φ : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜) (i : ι) :
    φ (rawHaarPacketShadow p n S T g i) =
      lpHaarLevelTrace (fun l k => lpHaarDyadicCoefficient 𝕜 p l k
        (outerSliceOperator T g φ (lpHaarDyadic 𝕜 p l k))) (n i)
        (lpHaarBlockParent (n i) (S i)) := by
  rw [rawHaarPacketShadow_eq_diagonal_sum, map_sum, lpHaarLevelTrace_parent,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [haarPacketReader]
  calc
    _ = weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
        (haarPacketWeight (n i) k) (haarPacketWeight_stronglyMeasurable (n i) k)
        (haarPacketWeight_norm_le (n i) k)
        (φ.compLpL p.val unitIntervalMeasure
          (T (tensorWith g (lpHaarDyadic 𝕜 p (n i) k.val)))) := by
      exact (weightedOuterReader_natural (𝕜 := 𝕜)
        (E := Lp 𝕜 1 unitIntervalMeasure) (F := 𝕜) (p := p.val)
        (haarPacketWeight (n i) k) (haarPacketWeight_stronglyMeasurable (n i) k)
        (haarPacketWeight_norm_le (n i) k) φ
        (T (tensorWith g (lpHaarDyadic 𝕜 p (n i) k.val)))).symm
    _ = _ := weightedOuterReader_haar_eq_radius_coefficient p (n i) k
      (outerSliceOperator T g φ (lpHaarDyadic 𝕜 p (n i) k.val))

theorem normalizedRawShadow_blockReader_tendsto (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (a : UniversalInnerPairRegisteredTraces p T r)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    Tendsto (fun m => pair.1.reader 𝕜 innerSplitExponent
      ((unitIntervalMeasure.real P.set : 𝕜)⁻¹ •
        rawHaarPacketShadow p r (fun m => lpHaarRefineAt P.level P.atoms (r m))
          T (pair.2.vector 𝕜 innerSplitExponent) m)) atTop
      (𝓝 (actualNormalizedOuterTrace p T a pair P)) := by
  have ht := ((a pair).limit ⟨P.level, P.atoms⟩).const_mul
    ((unitIntervalMeasure.real P.set : 𝕜)⁻¹)
  apply ht.congr'
  filter_upwards [hr.tendsto_atTop.eventually (eventually_ge_atTop P.level)] with m hm
  rw [map_smul, smul_eq_mul]
  have hformula := rawHaarPacketShadow_scalar_eq_levelTrace p r
    (fun m => lpHaarRefineAt P.level P.atoms (r m)) T
    (pair.2.vector 𝕜 innerSplitExponent) (pair.1.reader 𝕜 innerSplitExponent) m
  rw [lpHaarRefineAt_parent P.level P.atoms (r m) hm] at hformula
  simpa only [lpHaarDyadicSet, innerPairOuterSlice] using
    congrArg (fun z : 𝕜 => (unitIntervalMeasure.real P.set : 𝕜)⁻¹ * z) hformula.symm

end SurveyStatements.P5OperatorReduction
