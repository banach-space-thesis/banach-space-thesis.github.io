import SurveyStatements.P4Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Repeated finite rank-one decompositions for basis stabilization

Repeating a genuine finite basis decomposition of the identity makes its
partial sums uniformly bounded. This is the elementary finite-dimensional
input for a coefficient-path space with a monotone coordinate basis.
-/

noncomputable section
set_option autoImplicit false

open Set Finset Module

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [FiniteDimensional 𝕜 E]
variable {I : Type w} [Fintype I] [DecidableEq I]

def basisRankOne (b : Basis I 𝕜 E) (i : I) : E →L[𝕜] E :=
  (b.coord i).toContinuousLinearMap.smulRight (b i)

@[simp] lemma basisRankOne_apply (b : Basis I 𝕜 E) (i : I) (x : E) :
    basisRankOne b i x = (b.repr x i) • b i := rfl

lemma sum_basisRankOne (b : Basis I 𝕜 E) :
    ∑ i : I, basisRankOne b i = ContinuousLinearMap.id 𝕜 E := by
  ext x
  simpa using b.sum_repr x

def basisFrameBound (b : Basis I 𝕜 E) : ℝ := ∑ i : I, ‖basisRankOne b i‖

lemma basisFrameBound_nonneg (b : Basis I 𝕜 E) : 0 ≤ basisFrameBound b :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma norm_sum_basisRankOne_apply_le (b : Basis I 𝕜 E) (s : Finset I) (x : E) :
    ‖(∑ i ∈ s, basisRankOne b i) x‖ ≤ basisFrameBound b * ‖x‖ := by
  simp only [ContinuousLinearMap.sum_apply]
  calc
    ‖∑ i ∈ s, basisRankOne b i x‖ ≤ ∑ i ∈ s, ‖basisRankOne b i x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖basisRankOne b i‖ * ‖x‖ :=
      Finset.sum_le_sum fun _ _ => ContinuousLinearMap.le_opNorm _ _
    _ = (∑ i ∈ s, ‖basisRankOne b i‖) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ basisFrameBound b * ‖x‖ := mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun _ _ _ => norm_nonneg _)) (norm_nonneg x)

def repeatedFramePrefix (b : Basis I 𝕜 E) (m r : ℕ) (s : Finset I) : E →L[𝕜] E :=
  (r / m : ℝ) • ContinuousLinearMap.id 𝕜 E +
    (1 / m : ℝ) • ∑ i ∈ s, basisRankOne b i

lemma repeatedFramePrefix_norm_le (b : Basis I 𝕜 E) {m r : ℕ}
    (hm : 0 < m) (hr : r ≤ m) (hbound : basisFrameBound b ≤ m) (s : Finset I) (x : E) :
    ‖repeatedFramePrefix b m r s x‖ ≤ 2 * ‖x‖ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr' : (r : ℝ) ≤ m := by exact_mod_cast hr
  have hfirst : (r / m : ℝ) ≤ 1 := (div_le_one hm').mpr hr'
  have hsecond : (1 / m : ℝ) * basisFrameBound b ≤ 1 := by
    rw [one_div, ← div_eq_inv_mul]
    exact (div_le_one hm').mpr hbound
  simp only [repeatedFramePrefix, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  calc
    ‖(r / m : ℝ) • x + (1 / m : ℝ) • (∑ i ∈ s, basisRankOne b i) x‖ ≤
        ‖(r / m : ℝ) • x‖ + ‖(1 / m : ℝ) • (∑ i ∈ s, basisRankOne b i) x‖ := norm_add_le _ _
    _ = (r / m : ℝ) * ‖x‖ +
        (1 / m : ℝ) * ‖(∑ i ∈ s, basisRankOne b i) x‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
    _ ≤ (r / m : ℝ) * ‖x‖ + (1 / m : ℝ) * (basisFrameBound b * ‖x‖) :=
      add_le_add_left (mul_le_mul_of_nonneg_left (norm_sum_basisRankOne_apply_le b s x)
        (by positivity)) _
    _ = ((r / m : ℝ) + (1 / m : ℝ) * basisFrameBound b) * ‖x‖ := by ring
    _ ≤ 2 * ‖x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x)

end SurveyStatements.P4
