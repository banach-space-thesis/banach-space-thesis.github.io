import JLMS.WeakStarSequenceOperator
import JLMS.CZeroSubsequencePairs
import JLMS.PairedMatrix

/-!
# Operators obtained by pairing convergent norming functionals

Half-differences of consecutive functionals define a contraction into c₀.
Opposite-sign coordinate pairs define a contraction on c₀. The matrix of
their product through R is exactly the paired matrix used in the error estimate.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def pairedFunctional (φ : ℕ → (X →L[𝕜] 𝕜)) (n : ℕ) : X →L[𝕜] 𝕜 :=
  ((1 / 2 : ℝ) : 𝕜) • (φ (2 * n) - φ (2 * n + 1))

theorem norm_pairedFunctional_le (φ : ℕ → (X →L[𝕜] 𝕜))
    (hφ : ∀ n, ‖φ n‖ ≤ 1) (n : ℕ) : ‖pairedFunctional φ n‖ ≤ 1 := by
  rw [pairedFunctional, norm_smul, RCLike.norm_ofReal]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h := norm_sub_le (φ (2 * n)) (φ (2 * n + 1))
  linarith [hφ (2 * n), hφ (2 * n + 1)]

theorem pairedFunctional_tendsto_zero (φ : ℕ → (X →L[𝕜] 𝕜)) (ψ : X →L[𝕜] 𝕜)
    (ht : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (ψ x))) :
    ∀ x, Tendsto (fun n => pairedFunctional φ n x) atTop (𝓝 0) := by
  intro x
  have he : StrictMono (fun n : ℕ => 2 * n) := by intro i j hij; dsimp; omega
  have ho : StrictMono (fun n : ℕ => 2 * n + 1) := by intro i j hij; dsimp; omega
  simpa only [pairedFunctional, Function.comp_def, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul, sub_self, mul_zero] using
    (tendsto_const_nhds (x := ((1 / 2 : ℝ) : 𝕜))).mul
      (((ht x).comp he.tendsto_atTop).sub ((ht x).comp ho.tendsto_atTop))

def pairedNormingOperator (φ : ℕ → (X →L[𝕜] 𝕜)) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (ψ : X →L[𝕜] 𝕜) (ht : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (ψ x))) :
    X →L[𝕜] cZero 𝕜 :=
  weakStarSequenceOperator (pairedFunctional φ) 1 zero_le_one
    (norm_pairedFunctional_le φ hφ) (pairedFunctional_tendsto_zero φ ψ ht)

theorem norm_pairedNormingOperator_le (φ : ℕ → (X →L[𝕜] 𝕜))
    (hφ : ∀ n, ‖φ n‖ ≤ 1) (ψ : X →L[𝕜] 𝕜)
    (ht : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (ψ x))) :
    ‖pairedNormingOperator φ hφ ψ ht‖ ≤ 1 := norm_weakStarSequenceOperator_le _ _ _ _ _

@[simp] theorem pairedNormingOperator_apply (φ : ℕ → (X →L[𝕜] 𝕜))
    (hφ : ∀ n, ‖φ n‖ ≤ 1) (ψ : X →L[𝕜] 𝕜)
    (ht : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (ψ x))) (x : X) (i : ℕ) :
    pairedNormingOperator φ hφ ψ ht x i = pairedFunctional φ i x := rfl

theorem pairedNormingOperator_matrix (R : cZero 𝕜 →L[𝕜] X)
    (φ : ℕ → (X →L[𝕜] 𝕜)) (hφ : ∀ n, ‖φ n‖ ≤ 1) (ψ : X →L[𝕜] 𝕜)
    (s : ℕ → ℕ) (hs : StrictMono s)
    (ht : ∀ x, Tendsto (fun n => φ (s n) x) atTop (𝓝 (ψ x))) (i j : ℕ) :
    ((pairedNormingOperator (φ ∘ s) (fun n => hφ (s n)) ψ ht).comp R).comp
      (cZeroPairInsertion s hs) (cZeroUnit 𝕜 j) i =
    pairedMatrixCoefficient (fun i j => φ (s i) (R (cZeroUnit 𝕜 (s j)))) i j := by
  simp only [ContinuousLinearMap.comp_apply, cZeroPairInsertion_unit,
    pairedNormingOperator_apply, pairedFunctional, Function.comp_def,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, map_sub,
    ZeroAtInftyContinuousMap.sub_apply, smul_eq_mul,
    pairedMatrixCoefficient]
  ring

end JLMS
