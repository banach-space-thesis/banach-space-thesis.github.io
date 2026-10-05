import Posets.PaperOrdinalPowerDoublingTools
import JLMS.CZeroSumOperators

/-! An actual uniform equivalence between the finite heights n and 2n.
More generally each fixed positive multiplier of the height has a uniform
bound. The bound depends on the multiplier, not on n; no common uniform
equivalence with a fixed finite height is asserted. -/

noncomputable section
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance powerDoublingEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerDoublingEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerDoublingSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance powerDoublingSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

def paperOrdinalConstantSumCongr {I E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (he : ∀ x, ‖e x‖ ≤ C * ‖x‖) (hi : ∀ y, ‖e.symm y‖ ≤ C * ‖y‖) :
    JLMS.CZeroSum 𝕜 (fun _ : I => E) ≃L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => F) :=
  JLMS.CZeroSum.congrRight (fun _ => e) hC hC
    (fun _ => ContinuousLinearMap.opNorm_le_bound _ hC he)
    (fun _ => ContinuousLinearMap.opNorm_le_bound _ hC hi)

theorem paperOrdinalConstantSumCongr_norm_le {I E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (he : ∀ x, ‖e x‖ ≤ C * ‖x‖) (hi : ∀ y, ‖e.symm y‖ ≤ C * ‖y‖)
    (x : JLMS.CZeroSum 𝕜 (fun _ : I => E)) :
    ‖paperOrdinalConstantSumCongr e hC he hi x‖ ≤ C * ‖x‖ := by
  apply JLMS.CZeroSum.norm_le (mul_nonneg hC (norm_nonneg x))
  intro i
  exact (he (x i)).trans (mul_le_mul_of_nonneg_left (x.norm_apply_le_norm i) hC)

theorem paperOrdinalConstantSumCongr_symm_norm_le {I E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (he : ∀ x, ‖e x‖ ≤ C * ‖x‖) (hi : ∀ y, ‖e.symm y‖ ≤ C * ‖y‖)
    (x : JLMS.CZeroSum 𝕜 (fun _ : I => F)) :
    ‖(paperOrdinalConstantSumCongr e hC he hi).symm x‖ ≤ C * ‖x‖ := by
  apply JLMS.CZeroSum.norm_le (mul_nonneg hC (norm_nonneg x))
  intro i
  exact (hi (x i)).trans (mul_le_mul_of_nonneg_left (x.norm_apply_le_norm i) hC)

theorem paperOrdinalPowerMultiple_exists (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ∃ e : JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (((m + 1) * n : ℕ) : Ordinal)) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (n : Ordinal)),
      (∀ x, ‖e x‖ ≤ (512 : ℝ) ^ m * ‖x‖) ∧
      (∀ y, ‖e.symm y‖ ≤ (512 : ℝ) ^ m * ‖y‖) := by
  induction m with
  | zero =>
      rw [show ((0 + 1) * n : ℕ) = n by omega]
      exact ⟨ContinuousLinearEquiv.refl 𝕜 _, by simp, by simp⟩
  | succ m ih =>
      obtain ⟨e, he, hi⟩ := ih
      let g := paperOrdinalFinitePowerStep (𝕜 := 𝕜) c hc (m + 1) n (by omega) (by omega)
      let q := paperOrdinalConstantSumCongr (I := Set.Iio c.ord) e (by positivity) he hi
      let r := paperOrdinalFinitePowerReplication (𝕜 := 𝕜) c hc n hn
      refine ⟨g.trans (q.trans r.symm), ?_, ?_⟩
      · intro x
        change ‖r.symm (q (g x))‖ ≤ _
        calc
          _ ≤ 64 * ‖q (g x)‖ := paperOrdinalFinitePowerReplication_symm_norm_le c hc n hn _
          _ ≤ 64 * ((512 : ℝ) ^ m * ‖g x‖) := mul_le_mul_of_nonneg_left
            (paperOrdinalConstantSumCongr_norm_le e _ he hi _) (by norm_num)
          _ ≤ 64 * ((512 : ℝ) ^ m * (8 * ‖x‖)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (paperOrdinalFinitePowerStep_norm_le c hc _ _ _ _ x)
              (by positivity)) (by norm_num)
          _ = (512 : ℝ) ^ (m + 1) * ‖x‖ := by rw [pow_succ]; ring
      · intro y
        change ‖g.symm (q.symm (r y))‖ ≤ _
        calc
          _ ≤ 8 * ‖q.symm (r y)‖ := paperOrdinalFinitePowerStep_symm_norm_le c hc _ _ _ _ _
          _ ≤ 8 * ((512 : ℝ) ^ m * ‖r y‖) := mul_le_mul_of_nonneg_left
            (paperOrdinalConstantSumCongr_symm_norm_le e _ he hi _) (by norm_num)
          _ ≤ 8 * ((512 : ℝ) ^ m * (64 * ‖y‖)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (paperOrdinalFinitePowerReplication_norm_le c hc n hn y)
              (by positivity)) (by norm_num)
          _ = (512 : ℝ) ^ (m + 1) * ‖y‖ := by rw [pow_succ]; ring

def paperOrdinalPowerMultipleEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (((m + 1) * n : ℕ) : Ordinal)) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (n : Ordinal)) :=
  Classical.choose (paperOrdinalPowerMultiple_exists c hc n hn m)

theorem paperOrdinalPowerMultipleEquiv_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ‖(paperOrdinalPowerMultipleEquiv (𝕜 := 𝕜) c hc n hn m).toContinuousLinearMap‖ ≤ 512 ^ m :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (Classical.choose_spec (paperOrdinalPowerMultiple_exists c hc n hn m)).1

theorem paperOrdinalPowerMultipleEquiv_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ‖(paperOrdinalPowerMultipleEquiv (𝕜 := 𝕜) c hc n hn m).symm.toContinuousLinearMap‖ ≤ 512 ^ m :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (Classical.choose_spec (paperOrdinalPowerMultiple_exists c hc n hn m)).2

def paperOrdinalPowerDoublingEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (n : ℕ) (hn : 2 ≤ n) :
    JLMS.ordinalEndpointZero 𝕜 (c.ord ^ ((2 * n : ℕ) : Ordinal)) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (n : Ordinal)) :=
  paperOrdinalPowerMultipleEquiv c hc n hn 1

theorem paperOrdinalPowerDoublingEquiv_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n) :
    ‖(paperOrdinalPowerDoublingEquiv (𝕜 := 𝕜) c hc n hn).toContinuousLinearMap‖ ≤ 512 := by
  simpa only [pow_one] using paperOrdinalPowerMultipleEquiv_norm_le (𝕜 := 𝕜) c hc n hn 1

theorem paperOrdinalPowerDoublingEquiv_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n) :
    ‖(paperOrdinalPowerDoublingEquiv (𝕜 := 𝕜) c hc n hn).symm.toContinuousLinearMap‖ ≤ 512 := by
  simpa only [pow_one] using paperOrdinalPowerMultipleEquiv_symm_norm_le (𝕜 := 𝕜) c hc n hn 1

end Posets
