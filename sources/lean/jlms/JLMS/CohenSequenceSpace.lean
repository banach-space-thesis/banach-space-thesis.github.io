import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.Nat
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Banach-valued null sequences for simultaneous Cohen factorization

We use the actual Banach space `C₀(ℕ, B)`. Right multiplication by an element
of the ambient algebra preserves this space. A bounded right approximate
identity converges uniformly on each null sequence; the finite approximation
form below is what the constructive factorization uses.
-/

noncomputable section
open Filter Topology
open scoped ZeroAtInfty
namespace JLMS

variable {𝕜 B : Type*} [RCLike 𝕜] [NormedRing B] [NormedAlgebra 𝕜 B]

def cohenNullSequence (x : ℕ → B) (hx : Tendsto x atTop (𝓝 0)) : C₀(ℕ, B) where
  toFun := x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using hx

@[simp] theorem cohenNullSequence_apply (x : ℕ → B) (hx : Tendsto x atTop (𝓝 0))
    (n : ℕ) : cohenNullSequence x hx n = x n := rfl

def cohenSequenceMulRight (x : C₀(ℕ, B)) (b : B) : C₀(ℕ, B) where
  toFun n := x n * b
  continuous_toFun := x.continuous.mul continuous_const
  zero_at_infty' := by
    simpa using x.zero_at_infty'.mul (tendsto_const_nhds (x := b))

@[simp] theorem cohenSequenceMulRight_apply (x : C₀(ℕ, B)) (b : B) (n : ℕ) :
    cohenSequenceMulRight x b n = x n * b := rfl

theorem norm_cohenSequenceMulRight_le (x : C₀(ℕ, B)) (b : B) :
    ‖cohenSequenceMulRight x b‖ ≤ ‖x‖ * ‖b‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg x) (norm_nonneg b))).mpr
  intro n
  exact (norm_mul_le (x n) b).trans (mul_le_mul_of_nonneg_right
    (BoundedContinuousFunction.norm_coe_le_norm x.toBCF n) (norm_nonneg b))

@[simp] theorem cohenSequenceMulRight_one (x : C₀(ℕ, B)) :
    cohenSequenceMulRight x 1 = x := by ext n; simp

@[simp] theorem cohenSequenceMulRight_mul (x : C₀(ℕ, B)) (a b : B) :
    cohenSequenceMulRight x (a * b) =
      cohenSequenceMulRight (cohenSequenceMulRight x a) b := by
  ext n
  exact (mul_assoc _ _ _).symm

@[simp] theorem cohenSequenceMulRight_sub (x : C₀(ℕ, B)) (a b : B) :
    cohenSequenceMulRight x (a - b) =
      cohenSequenceMulRight x a - cohenSequenceMulRight x b := by
  ext n
  exact mul_sub _ _ _

@[simp] theorem cohenSequenceSub_mulRight (x y : C₀(ℕ, B)) (b : B) :
    cohenSequenceMulRight (x - y) b =
      cohenSequenceMulRight x b - cohenSequenceMulRight y b := by
  ext n
  exact sub_mul _ _ _

@[simp] theorem cohenSequenceMulRight_smul (x : C₀(ℕ, B)) (c : 𝕜) (b : B) :
    cohenSequenceMulRight x (c • b) = c • cohenSequenceMulRight x b := by
  ext n
  exact mul_smul_comm _ _ _

def cohenSequenceRightCLM (b : B) : C₀(ℕ, B) →L[𝕜] C₀(ℕ, B) :=
  ({ toFun x := cohenSequenceMulRight x b
     map_add' x y := by ext n; exact add_mul _ _ _
     map_smul' c x := by ext n; exact smul_mul_assoc _ _ _ } :
       C₀(ℕ, B) →ₗ[𝕜] C₀(ℕ, B)).mkContinuous ‖b‖
    (fun x => by simpa only [mul_comm] using norm_cohenSequenceMulRight_le x b)

@[simp] theorem cohenSequenceRightCLM_apply (b : B) (x : C₀(ℕ, B)) :
    cohenSequenceRightCLM (𝕜 := 𝕜) b x = cohenSequenceMulRight x b := rfl

/-- Finite approximation formulation of a bounded right approximate identity. -/
def HasBoundedRightApproximation (P : Submodule 𝕜 B) (M : ℝ) : Prop :=
  ∀ (s : Finset P) (ε : ℝ), 0 < ε →
    ∃ e ∈ P, ‖e‖ ≤ M ∧ ∀ z ∈ s, ‖z.val - z.val * e‖ ≤ ε

/-- Boundedness promotes pointwise approximation on the terms of a null
sequence to approximation in its supremum norm, simultaneously with one
additional element of the ideal. -/
theorem exists_rightApproximation_nullSequence (P : Submodule 𝕜 B) {M : ℝ}
    (hM : 0 ≤ M) (hAI : HasBoundedRightApproximation P M)
    (x : C₀(ℕ, B)) (hx : ∀ n, x n ∈ P) (s : P)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ e ∈ P, ‖e‖ ≤ M ∧ ‖s.val - s.val * e‖ ≤ η ∧
      ‖x - cohenSequenceMulRight x e‖ ≤ ε := by
  classical
  have htail : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
    have h := x.zero_at_infty'.norm
    simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop, norm_zero] using h
  have hMp : 0 < M + 1 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htail.eventually
    (eventually_lt_nhds (div_pos hε hMp)))
  let z : ℕ → P := fun n => ⟨x n, hx n⟩
  obtain ⟨e, he, hbound, happ⟩ := hAI (insert s ((Finset.range N).image z))
    (min η ε) (lt_min hη hε)
  refine ⟨e, he, hbound, (happ s (Finset.mem_insert_self _ _)).trans (min_le_left _ _), ?_⟩
  apply (BoundedContinuousFunction.norm_le hε.le).mpr
  intro n
  change ‖x n - x n * e‖ ≤ ε
  by_cases hn : n < N
  · exact (happ (z n) (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem z (Finset.mem_range.mpr hn)))).trans (min_le_right _ _)
  · calc
      ‖x n - x n * e‖ ≤ ‖x n‖ + ‖x n * e‖ := norm_sub_le _ _
      _ ≤ ‖x n‖ + ‖x n‖ * M := add_le_add_left
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hbound (norm_nonneg _))) _
      _ = ‖x n‖ * (M + 1) := by ring
      _ ≤ (ε / (M + 1)) * (M + 1) := mul_le_mul_of_nonneg_right
        (hN n (Nat.le_of_not_gt hn)).le hMp.le
      _ = ε := div_mul_cancel₀ ε hMp.ne'

end JLMS
