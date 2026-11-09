import SurveyStatements.P5Definitions
import SurveyStatements.P5Support.IntervalLpFunctionPartition
import SurveyStatements.P5Support.IntervalLpFunctionAffine

/-!
An actual normalized countable-partition isometry for the mixed Bochner space.
The underlying measure-partition, transport and scaling proofs are local ports
of genuine proofs in the adjacent ThesisCommon library. This module extends
its scalar interval construction to arbitrary normed vector-valued functions.
See `verification/P5-support-provenance.json` for exact source hashes.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace SurveyStatements.P5
open SurveyStatements.P5Support

section CoordinateEquivalence

variable {𝕜 ι : Type*} [RCLike 𝕜]
variable {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def vectorLpCoordinateValue (hp : 0 < p.toReal) (e : ∀ i, E i ≃ₗᵢ[𝕜] F i)
    (x : lp E p) : lp F p :=
  ⟨fun i => e i (x i), (memℓp_gen_iff hp).mpr (by
    simpa only [LinearIsometryEquiv.norm_map] using (lp.memℓp x).summable hp)⟩

def vectorLpCoordinateEquiv (hp : 0 < p.toReal) (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) :
    lp E p ≃ₗᵢ[𝕜] lp F p where
  toFun := vectorLpCoordinateValue hp e
  invFun := vectorLpCoordinateValue hp (fun i => (e i).symm)
  left_inv x := by
    apply lp.ext
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv x := by
    apply lp.ext
    funext i
    exact (e i).apply_symm_apply (x i)
  map_add' x y := by
    apply lp.ext
    funext i
    exact map_add (e i) (x i) (y i)
  map_smul' c x := by
    apply lp.ext
    funext i
    exact map_smul (e i) c (x i)
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    apply tsum_congr
    intro i
    change ‖e i (x i)‖ ^ p.toReal = ‖x i‖ ^ p.toReal
    rw [LinearIsometryEquiv.norm_map]

end CoordinateEquivalence

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Affine pullback, normalized to preserve the true vector-valued Lp norm. -/
def vectorLpAffine (hp : p ≠ ∞) (a : ℝ) (ha : 0 < a) :
    Lp E p (volume.restrict (Ioc a (2 * a))) ≃ₗᵢ[𝕜] Lp E p unitIntervalMeasure :=
  (lebesgueLpMeasureScaleEquiv (𝕜 := 𝕜) hp (ENNReal.ofReal a⁻¹)
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ha)) ENNReal.ofReal_ne_top).symm.trans
    (lebesgueLpTransport (intervalLpAffineEquiv a ha) (intervalLpAffineMeasure_restrict a ha))

theorem dyadicBlock_restrictedMeasure (n : ℕ) :
    unitIntervalMeasure.restrict (intervalLpDyadicBlock n) =
      volume.restrict (Ioc (intervalLpDyadicRadius (n + 1))
        (2 * intervalLpDyadicRadius (n + 1))) := by
  rw [unitIntervalMeasure, Measure.restrict_restrict_of_subset (intervalLpDyadicBlock_subset n)]
  congr 1
  unfold intervalLpDyadicBlock intervalLpDyadicRadius
  congr 1
  rw [pow_succ]
  ring

def vectorLpBlockEquiv (hp : p ≠ ∞) (n : ℕ) :
    Lp E p (unitIntervalMeasure.restrict (intervalLpDyadicBlock n))
      ≃ₗᵢ[𝕜] Lp E p unitIntervalMeasure :=
  (lebesgueLpMeasureCongr (𝕜 := 𝕜) (dyadicBlock_restrictedMeasure n)).trans
    (vectorLpAffine hp (intervalLpDyadicRadius (n + 1))
      (intervalLpDyadicRadius_pos (n + 1)))

/-- Partitioning the interval gives a genuine isometry to the countable lp sum,
including when `E` is the inner L1 Bochner space. -/
def vectorLpSelfSimilarity (hp : p ≠ ∞) :
    Lp E p unitIntervalMeasure ≃ₗᵢ[𝕜]
      lp (fun _ : ℕ => Lp E p unitIntervalMeasure) p :=
  (lebesgueLpPartitionEquiv hp intervalLpDyadicBlock (fun _ => measurableSet_Ioc)
    intervalLpDyadicBlock_disjoint intervalLpDyadicBlock_cover).trans
    (vectorLpCoordinateEquiv
      (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp)
      (vectorLpBlockEquiv (𝕜 := 𝕜) (E := E) hp))

def mixedNormSelfSimilarity (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    MixedNorm 𝕜 p ≃ₗᵢ[𝕜] lp (fun _ : ℕ => MixedNorm 𝕜 p) p :=
  vectorLpSelfSimilarity hp

end SurveyStatements.P5
