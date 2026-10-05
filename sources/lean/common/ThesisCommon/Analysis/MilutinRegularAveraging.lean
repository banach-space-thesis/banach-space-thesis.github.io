import ThesisCommon.Analysis.MilutinAveragingExtension
import Mathlib.Topology.Metrizable.Basic

/-! Regular averaging propagates through a sequential inverse limit.
This completes the operator assertion of Rosenthal Lemma 2.12: the averaging
operator is constructed by composing the bonding averages on cylinders and
extending to their norm closure. -/

noncomputable section
namespace ThesisCommon
open TopologicalSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : ℕ → Type*} [∀ n, TopologicalSpace (K n)]
  [∀ n, CompactSpace (K n)] [∀ n, T2Space (K n)]
variable (φ : ∀ n, C(K (n + 1), K n))
variable (hφ : ∀ n, Function.Surjective (φ n))
variable (A : ∀ n, C(K (n + 1), 𝕜) →L[𝕜] C(K n, 𝕜))

def milutinIteratedAverage (A : ∀ n, C(K (n + 1), 𝕜) →L[𝕜] C(K n, 𝕜)) :
    ∀ n, C(K n, 𝕜) →L[𝕜] C(K 0, 𝕜)
  | 0 => ContinuousLinearMap.id 𝕜 C(K 0, 𝕜)
  | n + 1 => (milutinIteratedAverage A n).comp (A n)

theorem norm_milutinIteratedAverage_le (hA : ∀ n, ‖A n‖ ≤ 1) (n : ℕ) :
    ‖milutinIteratedAverage A n‖ ≤ 1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact (mul_le_mul ih (hA n) (norm_nonneg _) zero_le_one).trans (by simp)

theorem milutinIteratedAverage_compatible
    (hAJ : ∀ n, (A n).comp (continuousMapPullback (φ n)) =
      ContinuousLinearMap.id 𝕜 C(K n, 𝕜))
    (n : ℕ) (f : C(K n, 𝕜)) :
    milutinIteratedAverage A (n + 1) (f.comp (φ n)) = milutinIteratedAverage A n f := by
  change milutinIteratedAverage A n (A n (f.comp (φ n))) = milutinIteratedAverage A n f
  have hf : A n (f.comp (φ n)) = f :=
    congrArg (fun L : C(K n, 𝕜) →L[𝕜] C(K n, 𝕜) => L f) (hAJ n)
  rw [hf]

def milutinLimitAverage (hA : ∀ n, ‖A n‖ ≤ 1)
    (hAJ : ∀ n, (A n).comp (continuousMapPullback (φ n)) =
      ContinuousLinearMap.id 𝕜 C(K n, 𝕜)) :
    C(MilutinInverseLimit φ, 𝕜) →L[𝕜] C(K 0, 𝕜) :=
  milutinAverageExtension φ hφ (milutinIteratedAverage A)
    (milutinIteratedAverage_compatible φ A hAJ) (norm_milutinIteratedAverage_le A hA)

theorem norm_milutinLimitAverage_le (hA : ∀ n, ‖A n‖ ≤ 1)
    (hAJ : ∀ n, (A n).comp (continuousMapPullback (φ n)) =
      ContinuousLinearMap.id 𝕜 C(K n, 𝕜)) :
    ‖milutinLimitAverage φ hφ A hA hAJ‖ ≤ 1 :=
  norm_milutinAverageExtension_le _ _ _ _ _

theorem milutinLimitAverage_comp_pullback (hA : ∀ n, ‖A n‖ ≤ 1)
    (hAJ : ∀ n, (A n).comp (continuousMapPullback (φ n)) =
      ContinuousLinearMap.id 𝕜 C(K n, 𝕜)) :
    (milutinLimitAverage φ hφ A hA hAJ).comp
      (continuousMapPullback (milutinLimitProjection φ 0)) =
      ContinuousLinearMap.id 𝕜 C(K 0, 𝕜) := by
  apply ContinuousLinearMap.ext
  intro f
  exact milutinAverageExtension_apply_cylinder φ hφ (milutinIteratedAverage A)
    (milutinIteratedAverage_compatible φ A hAJ) (norm_milutinIteratedAverage_le A hA) 0 f

include hφ in
/-- The sequential inverse-limit averaging lemma, with the original surjectivity
and contractive averaging assumptions on every bonding map. -/
theorem milutin_inverse_limit_averaging
    (hA : ∀ n, ∃ A : C(K (n + 1), 𝕜) →L[𝕜] C(K n, 𝕜),
      ‖A‖ ≤ 1 ∧ A.comp (continuousMapPullback (φ n)) =
        ContinuousLinearMap.id 𝕜 C(K n, 𝕜)) :
    ∃ A : C(MilutinInverseLimit φ, 𝕜) →L[𝕜] C(K 0, 𝕜),
      ‖A‖ ≤ 1 ∧ A.comp (continuousMapPullback (milutinLimitProjection φ 0)) =
        ContinuousLinearMap.id 𝕜 C(K 0, 𝕜) := by
  choose A hAn hAJ using hA
  exact ⟨milutinLimitAverage φ hφ A hAn hAJ,
    norm_milutinLimitAverage_le φ hφ A hAn hAJ,
    milutinLimitAverage_comp_pullback φ hφ A hAn hAJ⟩

include hφ in
theorem milutin_inverse_limit_regular_averaging [Nonempty (K 0)]
    (hA : ∀ n, ∃ A : C(K (n + 1), 𝕜) →L[𝕜] C(K n, 𝕜),
      ‖A‖ ≤ 1 ∧ A.comp (continuousMapPullback (φ n)) =
        ContinuousLinearMap.id 𝕜 C(K n, 𝕜)) :
    ∃ A : C(MilutinInverseLimit φ, 𝕜) →L[𝕜] C(K 0, 𝕜),
      ‖A‖ = 1 ∧ A.comp (continuousMapPullback (milutinLimitProjection φ 0)) =
        ContinuousLinearMap.id 𝕜 C(K 0, 𝕜) := by
  obtain ⟨A, hAn, hAJ⟩ := milutin_inverse_limit_averaging φ hφ hA
  refine ⟨A, le_antisymm hAn ?_, hAJ⟩
  have h := ContinuousLinearMap.opNorm_comp_le A
    (continuousMapPullback (𝕜 := 𝕜) (milutinLimitProjection φ 0))
  rw [hAJ, ContinuousLinearMap.norm_id] at h
  apply h.trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (norm_continuousMapPullback_le (𝕜 := 𝕜) (milutinLimitProjection φ 0)) (norm_nonneg A)

instance milutinInverseLimitMetrizableSpace [∀ n, MetrizableSpace (K n)] :
    MetrizableSpace (MilutinInverseLimit φ) := by
  letI : ∀ n, MetricSpace (K n) := fun n => metrizableSpaceMetric (K n)
  letI : MetricSpace (∀ n, K n) := PiCountable.metricSpace
  exact inferInstanceAs (MetrizableSpace {z : ∀ n, K n // ∀ n, φ n (z (n + 1)) = z n})

end ThesisCommon
