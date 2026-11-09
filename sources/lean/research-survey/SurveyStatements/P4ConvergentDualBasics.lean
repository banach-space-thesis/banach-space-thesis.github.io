import SurveyStatements.P4Goldstine
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! Finite coordinate vectors and their genuine norm density in the kernel
of limit evaluation on the concrete convergent-sequence space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter Topology
open scoped OnePoint BigOperators

namespace SurveyStatements.P4

variable {𝕜 Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def convergentDualSingleLinearMap (n : ℕ) : Y →ₗ[𝕜] C(OnePoint ℕ, Y) where
  toFun y := OnePoint.continuousMapMkNat (fun k => if k = n then y else 0) 0
    (tendsto_const_nhds.congr' ((eventually_ge_atTop (n + 1)).mono fun k hk => by
      have hkn : k ≠ n := by omega
      simp only [if_neg hkn]))
  map_add' x y := by
    ext q
    cases q using OnePoint.rec with
    | infty => change (0 : Y) = 0 + 0; simp
    | coe k =>
      change (if k = n then x + y else 0) =
        (if k = n then x else 0) + (if k = n then y else 0)
      split_ifs <;> simp
  map_smul' a y := by
    ext q
    cases q using OnePoint.rec with
    | infty => change (0 : Y) = a • 0; simp
    | coe k =>
      change (if k = n then a • y else 0) = a • (if k = n then y else 0)
      split_ifs <;> simp

lemma convergentDualSingleLinearMap_norm_le (n : ℕ) (y : Y) :
    ‖convergentDualSingleLinearMap (𝕜 := 𝕜) n y‖ ≤ ‖y‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg y)).mpr
  intro q
  cases q using OnePoint.rec with
  | infty => change ‖(0 : Y)‖ ≤ ‖y‖; simpa only [norm_zero] using norm_nonneg y
  | coe k =>
    change ‖if k = n then y else 0‖ ≤ ‖y‖
    split_ifs <;> simp

def convergentDualSingle (n : ℕ) : Y →L[𝕜] C(OnePoint ℕ, Y) :=
  (convergentDualSingleLinearMap (𝕜 := 𝕜) n).mkContinuous 1
    (fun y => by simpa only [one_mul] using convergentDualSingleLinearMap_norm_le n y)

@[simp] lemma convergentDualSingle_coe (n k : ℕ) (y : Y) :
    convergentDualSingle (𝕜 := 𝕜) n y (k : OnePoint ℕ) = if k = n then y else 0 := rfl

@[simp] lemma convergentDualSingle_infty (n : ℕ) (y : Y) :
    convergentDualSingle (𝕜 := 𝕜) n y (∞ : OnePoint ℕ) = 0 := rfl

lemma convergentDualSingle_sum_coe (F : Finset ℕ) (x : ℕ → Y) (k : ℕ) :
    (∑ n ∈ F, convergentDualSingle (𝕜 := 𝕜) n (x n)) (k : OnePoint ℕ) =
      if k ∈ F then x k else 0 := by
  simp [ContinuousMap.sum_apply, eq_comm]

lemma convergentDualSingle_sum_norm_le (F : Finset ℕ) (x : ℕ → Y)
    (C : ℝ) (hC : 0 ≤ C) (hx : ∀ n ∈ F, ‖x n‖ ≤ C) :
    ‖∑ n ∈ F, convergentDualSingle (𝕜 := 𝕜) n (x n)‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hC).mpr
  intro q
  cases q using OnePoint.rec with
  | infty => simpa only [ContinuousMap.sum_apply, convergentDualSingle_infty,
      Finset.sum_const_zero, norm_zero] using hC
  | coe k =>
    rw [convergentDualSingle_sum_coe]
    split_ifs with hk
    · exact hx k hk
    · simpa only [norm_zero] using hC

def convergentDualZeroTruncate (n : ℕ) (z : C(OnePoint ℕ, Y)) : C(OnePoint ℕ, Y) :=
  ∑ k ∈ Finset.range n, convergentDualSingle (𝕜 := 𝕜) k (z (k : OnePoint ℕ))

theorem convergentDualZeroTruncate_tendsto (z : C(OnePoint ℕ, Y)) (hz : z ∞ = 0) :
    Tendsto (fun n => convergentDualZeroTruncate (𝕜 := 𝕜) n z) atTop (𝓝 z) := by
  have ht : Tendsto (fun n : ℕ => z (n : OnePoint ℕ)) atTop (𝓝 (0 : Y)) := by
    simpa only [hz] using (OnePoint.continuous_iff_from_nat z).mp z.continuous
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ((ContinuousMap.norm_le _ (half_pos hε).le).mpr ?_) (half_lt_self hε)
  intro q
  cases q using OnePoint.rec with
  | infty =>
    simp only [ContinuousMap.sub_apply, convergentDualZeroTruncate, ContinuousMap.sum_apply,
      convergentDualSingle_infty, Finset.sum_const_zero, hz, sub_self, norm_zero]
    positivity
  | coe k =>
    change ‖(convergentDualZeroTruncate (𝕜 := 𝕜) n z) (k : OnePoint ℕ) -
      z (k : OnePoint ℕ)‖ ≤ ε / 2
    rw [convergentDualZeroTruncate, convergentDualSingle_sum_coe]
    by_cases hk : k ∈ Finset.range n
    · simp only [if_pos hk, sub_self, norm_zero]
      positivity
    · rw [if_neg hk, zero_sub, norm_neg]
      have hkn : n ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
      simpa only [dist_zero_right] using (hN k (hn.trans hkn)).le

def convergentDualCoordinate (Φ : StrongDual 𝕜 C(OnePoint ℕ, Y)) (n : ℕ) : StrongDual 𝕜 Y :=
  Φ.comp (convergentDualSingle (𝕜 := 𝕜) n)

@[simp] lemma convergentDualCoordinate_apply (Φ : StrongDual 𝕜 C(OnePoint ℕ, Y))
    (n : ℕ) (y : Y) : convergentDualCoordinate Φ n y =
      Φ (convergentDualSingle (𝕜 := 𝕜) n y) := rfl

end SurveyStatements.P4
