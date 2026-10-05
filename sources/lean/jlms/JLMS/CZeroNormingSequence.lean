import JLMS.PointDifferenceEvaluation
import JLMS.PhaseFunctions

/-!
# Convergent norming point functionals for a sequence of C₀ functions

Choose a point where each function exceeds a fixed positive threshold and
align its value with a scalar phase. Compact scattered sequential compactness
extracts convergent points in the one-point compactification; scalar compactness
extracts convergent phases. The resulting norming functionals converge weak-star.
This supplies a direct factorization route for scattered C₀ codomains.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

local instance cZeroNormingDualGroup : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance cZeroNormingDualSpace : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

def onePointEvaluation (x : OnePoint K) : CZero 𝕜 K →L[𝕜] 𝕜 :=
  OnePoint.rec 0 (fun k => evaluation k) x

@[simp] theorem onePointEvaluation_apply (x : OnePoint K) (f : CZero 𝕜 K) :
    onePointEvaluation x f = extendCZeroOnePoint f x := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe k => rfl

theorem norm_onePointEvaluation_le (x : OnePoint K) :
    ‖onePointEvaluation (𝕜 := 𝕜) x‖ ≤ 1 := by
  induction x using OnePoint.rec with
  | infty => change ‖(0 : CZero 𝕜 K →L[𝕜] 𝕜)‖ ≤ 1; simp
  | coe k => exact norm_evaluation_le k

theorem exists_CZero_point_norm_gt (f : CZero 𝕜 K) {γ : ℝ}
    (hγ : 0 ≤ γ) (hlarge : γ < ‖f‖) : ∃ k : K, γ < ‖f k‖ := by
  by_contra h
  push_neg at h
  exact hlarge.not_ge ((BoundedContinuousFunction.norm_le hγ).mpr h)

/-- A uniformly large function sequence admits norming unit-ball functionals
with a common weak-star-convergent subsequence. -/
theorem exists_convergent_CZero_normingSequence (hK : IsScattered K)
    (f : ℕ → CZero 𝕜 K) {γ : ℝ} (hγ : 0 < γ) (hlarge : ∀ n, γ < ‖f n‖) :
    ∃ φ : ℕ → (CZero 𝕜 K →L[𝕜] 𝕜), (∀ n, ‖φ n‖ ≤ 1) ∧
      (∀ n, γ < RCLike.re (φ n (f n)) ∧
        φ n (f n) = (RCLike.re (φ n (f n)) : 𝕜)) ∧
      ∃ ψ : CZero 𝕜 K →L[𝕜] 𝕜, ∃ s : ℕ → ℕ, StrictMono s ∧
        ∀ g : CZero 𝕜 K, Tendsto (fun n => φ (s n) g) atTop (𝓝 (ψ g)) := by
  letI : NormSMulClass 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) :=
    @NormedSpace.toNormSMulClass 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) _ _ _
  choose p hp using fun n => exists_CZero_point_norm_gt (f n) hγ.le (hlarge n)
  let α (n : ℕ) : 𝕜 := scalarPhase (f n (p n))
  let φ (n : ℕ) : CZero 𝕜 K →L[𝕜] 𝕜 := α n • evaluation (p n)
  have hφ (n : ℕ) : ‖φ n‖ ≤ 1 := by
    change ‖α n • evaluation (𝕜 := 𝕜) (p n)‖ ≤ 1
    rw [norm_smul, norm_scalarPhase, one_mul]
    exact norm_evaluation_le _
  have hφlarge (n : ℕ) : γ < RCLike.re (φ n (f n)) ∧
      φ n (f n) = (RCLike.re (φ n (f n)) : 𝕜) := by
    change γ < RCLike.re (scalarPhase (f n (p n)) * f n (p n)) ∧
      scalarPhase (f n (p n)) * f n (p n) =
        (RCLike.re (scalarPhase (f n (p n)) * f n (p n)) : 𝕜)
    rw [scalarPhase_mul, RCLike.ofReal_re]
    exact ⟨hp n, rfl⟩
  obtain ⟨x, r, hr, ht⟩ := scattered_compact_subsequence (scattered_onePoint hK)
    (fun n => (p n : OnePoint K))
  let B := ↥(Metric.closedBall (0 : 𝕜) 1)
  letI : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : 𝕜) 1)
  let a (n : ℕ) : B := ⟨α (r n), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_scalarPhase]⟩
  obtain ⟨z, q, hq, hqz⟩ := SeqCompactSpace.tendsto_subseq a
  have haz : Tendsto (fun n => α (r (q n))) atTop (𝓝 z.val) :=
    continuous_subtype_val.tendsto z |>.comp hqz
  let ψ : CZero 𝕜 K →L[𝕜] 𝕜 := z.val • onePointEvaluation x
  refine ⟨φ, hφ, hφlarge, ψ, r ∘ q, hr.comp hq, ?_⟩
  intro g
  have hg : Tendsto (fun n => g (p (r (q n)))) atTop (𝓝 (extendCZeroOnePoint g x)) :=
    (extendCZeroOnePoint g).continuous.tendsto x |>.comp (ht.comp hq.tendsto_atTop)
  simpa only [φ, ψ, Function.comp_def, ContinuousLinearMap.smul_apply,
    evaluation_apply, onePointEvaluation_apply, smul_eq_mul] using haz.mul hg

end JLMS
