import PL1CD.LimsupSeminorm
import PL1.KernelTranslations
import Mathlib.Order.Filter.Cofinite

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace PL1CD.Variation

variable {𝕜 E Z : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

def finiteVariation {ι : Type*} [Fintype ι] (e f : ι → E) : Seminorm 𝕜 (E →L[𝕜] Z) :=
  Seminorm.of (fun T => (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖T (e i - f i)‖)
    (by
      intro T U
      calc
        _ ≤ (Fintype.card ι : ℝ)⁻¹ *
            ∑ i, (‖T (e i - f i)‖ + ‖U (e i - f i)‖) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
          exact Finset.sum_le_sum (fun i _ => norm_add_le _ _)
        _ = _ := by rw [Finset.sum_add_distrib, mul_add])
    (by
      intro a T
      simp only [smul_apply, norm_smul, ← Finset.mul_sum]
      ring)

theorem finiteVariation_le {ι : Type*} [Fintype ι] [Nonempty ι] (e f : ι → E)
    (he : ∀ i, ‖e i‖ ≤ 1) (hf : ∀ i, ‖f i‖ ≤ 1) (T : E →L[𝕜] Z) :
    finiteVariation e f T ≤ 2 * ‖T‖ := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖T (e i - f i)‖ ≤ _
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, 2 * ‖T‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum
      intro i _
      have hnorm : ‖e i - f i‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [he i, hf i])
      calc
        _ ≤ ‖T‖ * ‖e i - f i‖ := T.le_opNorm _
        _ ≤ ‖T‖ * 2 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg T)
        _ = _ := mul_comm _ _
    _ = 2 * ‖T‖ := by simp [hc]

theorem finiteVariation_comp_le {ι : Type*} [Fintype ι] (e f : ι → E)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] Z) (W : Z →L[𝕜] F) :
    finiteVariation e f (W.comp T) ≤ ‖W‖ * finiteVariation e f T := by
  change (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖W (T (e i - f i))‖ ≤
    ‖W‖ * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖T (e i - f i)‖)
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖W‖ * ‖T (e i - f i)‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum (fun i _ => W.le_opNorm _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem finiteVariation_comp_ge {ι : Type*} [Fintype ι] (e f : ι → E)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] Z) (W : Z →L[𝕜] F) (c : ℝ)
    (hlower : ∀ z, c * ‖z‖ ≤ ‖W z‖) :
    c * finiteVariation e f T ≤ finiteVariation e f (W.comp T) := by
  change c * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖T (e i - f i)‖) ≤
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖W (T (e i - f i))‖
  calc
    _ = (Fintype.card ι : ℝ)⁻¹ * ∑ i, c * ‖T (e i - f i)‖ := by
      rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => hlower _)) (inv_nonneg.mpr (Nat.cast_nonneg _))

def averageSeminorm (p : ℕ → Seminorm 𝕜 E) (N : ℕ) : Seminorm 𝕜 E :=
  (N : ℝ≥0)⁻¹ • ∑ n ∈ Finset.range N, p n

theorem averageSeminorm_apply (p : ℕ → Seminorm 𝕜 E) (N : ℕ) (x : E) :
    averageSeminorm p N x = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, p n x := by
  simp [averageSeminorm, smul_apply, sum_apply, NNReal.smul_def]

theorem averageSeminorm_le (p : ℕ → Seminorm 𝕜 E) (C : ℝ)
    (hbound : ∀ n x, p n x ≤ C * ‖x‖) (hC : 0 ≤ C) (N : ℕ) (x : E) :
    averageSeminorm p N x ≤ C * ‖x‖ := by
  rw [averageSeminorm_apply]
  by_cases hN : N = 0
  · simp [hN, mul_nonneg hC (norm_nonneg x)]
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    calc
      _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, C * ‖x‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => hbound n x))
          (inv_nonneg.mpr (Nat.cast_nonneg N))
      _ = C * ‖x‖ := by simp [hN']

variable (𝕜 Z)

abbrev HaarL1 := Lp 𝕜 1 PL1.Walsh.haar

def levelSeminorm (M : ℕ → ℕ) (n : ℕ) : Seminorm 𝕜 (HaarL1 𝕜 →L[𝕜] Z) :=
  finiteVariation
    (fun a : PL1.FiniteCoordinateKernels.Assignments (Finset.range (M (n + 1))) =>
      PL1.ExplicitMartingale.kernelL1 𝕜 (M (n + 1))
        (PL1.FiniteCoordinateKernels.extend _ a))
    (fun a => PL1.ExplicitMartingale.kernelL1 𝕜 (M n)
      (PL1.FiniteCoordinateKernels.extend _ a))

theorem levelSeminorm_le (M : ℕ → ℕ) (n : ℕ) (T : HaarL1 𝕜 →L[𝕜] Z) :
    levelSeminorm 𝕜 Z M n T ≤ 2 * ‖T‖ :=
  finiteVariation_le _ _
    (fun _ => (PL1.ExplicitMartingale.norm_kernelL1 𝕜 _ _).le)
    (fun _ => (PL1.ExplicitMartingale.norm_kernelL1 𝕜 _ _).le) T

def endpointSeminorm (M N : ℕ → ℕ) (s : ℕ) :
    Seminorm 𝕜 (HaarL1 𝕜 →L[𝕜] Z) := averageSeminorm (levelSeminorm 𝕜 Z M) (N s)

theorem endpointSeminorm_le (M N : ℕ → ℕ) (s : ℕ) (T : HaarL1 𝕜 →L[𝕜] Z) :
    endpointSeminorm 𝕜 Z M N s T ≤ (2 : ℝ≥0) * ‖T‖ :=
  averageSeminorm_le _ 2 (levelSeminorm_le 𝕜 Z M) (by norm_num) (N s) T

theorem alongInfinite_neBot {H : Set ℕ} (hH : H.Infinite) :
    (atTop ⊓ 𝓟 H).NeBot := by
  simpa only [Nat.cofinite_eq_atTop] using hH.cofinite_inf_principal_neBot

def averagedVariation (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite) :
    Seminorm 𝕜 (HaarL1 𝕜 →L[𝕜] Z) := by
  letI := alongInfinite_neBot hH
  exact PL1CD.limsupSeminorm (endpointSeminorm 𝕜 Z M N) 2
    (endpointSeminorm_le 𝕜 Z M N) (atTop ⊓ 𝓟 H)

theorem averagedVariation_le (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (T : HaarL1 𝕜 →L[𝕜] Z) : averagedVariation 𝕜 Z M N H hH T ≤ 2 * ‖T‖ := by
  let := alongInfinite_neBot hH
  exact PL1CD.limsupSeminorm_le _ 2 (endpointSeminorm_le 𝕜 Z M N) _ T

theorem averagedVariation_continuous (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite) :
    Continuous (averagedVariation 𝕜 Z M N H hH) := by
  let := alongInfinite_neBot hH
  exact PL1CD.limsupSeminorm_continuous _ 2 (endpointSeminorm_le 𝕜 Z M N) _

end PL1CD.Variation
