import SurveyStatements.P4Definitions
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-! Actual freeze projections and convergent-sequence lifts on
`C(OnePoint ℕ, Y)`, the concrete Banach model of `c(Y)`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter Topology
open scoped OnePoint

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def convergentFreezeIndex (n : ℕ) : C(OnePoint ℕ, OnePoint ℕ) :=
  OnePoint.continuousMapMkNat (fun k => ((min n k : ℕ) : OnePoint ℕ)) (n : OnePoint ℕ)
    (tendsto_const_nhds.congr' ((eventually_ge_atTop n).mono fun k hk => by
      simp only [min_eq_left hk]))

@[simp] lemma convergentFreezeIndex_coe (n k : ℕ) :
    convergentFreezeIndex n (k : OnePoint ℕ) = ((min n k : ℕ) : OnePoint ℕ) := rfl

@[simp] lemma convergentFreezeIndex_infty (n : ℕ) :
    convergentFreezeIndex n (∞ : OnePoint ℕ) = (n : OnePoint ℕ) := rfl

def convergentFreezeLinearMap (n : ℕ) :
    C(OnePoint ℕ, Y) →ₗ[𝕜] C(OnePoint ℕ, Y) where
  toFun z := z.comp (convergentFreezeIndex n)
  map_add' z t := by ext q; rfl
  map_smul' a z := by ext q; rfl

lemma convergentFreezeLinearMap_norm_le (n : ℕ) (z : C(OnePoint ℕ, Y)) :
    ‖convergentFreezeLinearMap (𝕜 := 𝕜) n z‖ ≤ ‖z‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg z)).mpr
  intro q
  exact z.norm_coe_le_norm _

def convergentFreeze (n : ℕ) : C(OnePoint ℕ, Y) →L[𝕜] C(OnePoint ℕ, Y) :=
  (convergentFreezeLinearMap (𝕜 := 𝕜) n).mkContinuous 1
    (fun z => by simpa only [one_mul] using convergentFreezeLinearMap_norm_le n z)

@[simp] lemma convergentFreeze_coe (n k : ℕ) (z : C(OnePoint ℕ, Y)) :
    convergentFreeze (𝕜 := 𝕜) n z (k : OnePoint ℕ) = z ((min n k : ℕ) : OnePoint ℕ) := rfl

@[simp] lemma convergentFreeze_infty (n : ℕ) (z : C(OnePoint ℕ, Y)) :
    convergentFreeze (𝕜 := 𝕜) n z (∞ : OnePoint ℕ) = z (n : OnePoint ℕ) := rfl

lemma norm_convergentFreeze_le_one (n : ℕ) :
    ‖convergentFreeze (𝕜 := 𝕜) (Y := Y) n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simpa only [one_mul] using convergentFreezeLinearMap_norm_le (𝕜 := 𝕜) n z

lemma convergentFreeze_comp (n m : ℕ) :
    (convergentFreeze (𝕜 := 𝕜) (Y := Y) n).comp (convergentFreeze m) =
      convergentFreeze (min n m) := by
  apply ContinuousLinearMap.ext
  intro z
  ext q
  cases q using OnePoint.rec with
  | infty => simp [ContinuousLinearMap.comp_apply, min_comm]
  | coe k => simp [ContinuousLinearMap.comp_apply, min_left_comm, min_assoc, min_comm]

theorem convergentFreeze_tendsto (z : C(OnePoint ℕ, Y)) :
    Tendsto (fun n => convergentFreeze (𝕜 := 𝕜) n z) atTop (𝓝 z) := by
  have ht : Tendsto (fun n : ℕ => z (n : OnePoint ℕ)) atTop (𝓝 (z ∞)) :=
    (OnePoint.continuous_iff_from_nat z).mp z.continuous
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ((ContinuousMap.norm_le _ (half_pos hε).le).mpr ?_)
    (half_lt_self hε)
  intro q
  cases q using OnePoint.rec with
  | infty =>
      change ‖z (n : OnePoint ℕ) - z ∞‖ ≤ ε / 2
      have h := hN n hn
      rw [dist_eq_norm] at h
      linarith
  | coe k =>
      change ‖z ((min n k : ℕ) : OnePoint ℕ) - z (k : OnePoint ℕ)‖ ≤ ε / 2
      by_cases hkn : k ≤ n
      · rw [min_eq_right hkn, sub_self, norm_zero]
        positivity
      · rw [min_eq_left (le_of_not_ge hkn)]
        have hn' := hN n hn
        have hk' := hN k (hn.trans (le_of_not_ge hkn))
        rw [dist_eq_norm] at hn' hk'
        calc
          ‖z (n : OnePoint ℕ) - z (k : OnePoint ℕ)‖ ≤
              ‖z (n : OnePoint ℕ) - z ∞‖ + ‖z ∞ - z (k : OnePoint ℕ)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ = ‖z (n : OnePoint ℕ) - z ∞‖ + ‖z (k : OnePoint ℕ) - z ∞‖ := by
            rw [norm_sub_rev (z ∞) (z (k : OnePoint ℕ))]
          _ ≤ ε / 2 := by linarith

def convergentLiftLinearMap (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y)
    (hpoint : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x))) :
    X →ₗ[𝕜] C(OnePoint ℕ, Y) where
  toFun x := OnePoint.continuousMapMkNat (fun n => A n x) (T x) (hpoint x)
  map_add' x y := by
    ext q
    cases q using OnePoint.rec <;> simp only [OnePoint.continuousMapMkNat, map_add] <;> rfl
  map_smul' a x := by
    ext q
    cases q using OnePoint.rec <;> simp only [OnePoint.continuousMapMkNat, map_smul] <;> rfl

lemma convergentLiftLinearMap_norm_le (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y)
    (hpoint : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x)))
    {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C) (x : X) :
    ‖convergentLiftLinearMap A T hpoint x‖ ≤ max C ‖T‖ * ‖x‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (le_max_right _ _ |>.trans' (norm_nonneg _))
    (norm_nonneg x))).mpr
  intro q
  cases q using OnePoint.rec with
  | infty =>
      exact (T.le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))
  | coe n =>
      exact ((A n).le_opNorm x).trans (mul_le_mul_of_nonneg_right
        ((hA n).trans (le_max_left _ _)) (norm_nonneg x))

def convergentLift (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y)
    (hpoint : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x)))
    {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C) : X →L[𝕜] C(OnePoint ℕ, Y) :=
  (convergentLiftLinearMap A T hpoint).mkContinuous (max C ‖T‖)
    (convergentLiftLinearMap_norm_le A T hpoint hA)

lemma eval_infty_comp_convergentLift (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y)
    (hpoint : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x)))
    {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C) :
    (ContinuousMap.evalCLM 𝕜 (∞ : OnePoint ℕ)).comp (convergentLift A T hpoint hA) = T := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

end SurveyStatements.P4
