import Posets.SzlenkOrdinalBoundsApproximation
import Posets.SzlenkIdealAddition
import Posets.SzlenkOrdinalNaturalSum
import JLMS.CZeroSumFinite

/-! The Szlenk upper bound for an actual dependent Banach c₀ sum. -/
noncomputable section
open Set Topology Filter
open scoped NaturalOps
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {I : Type*} {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
set_option synthInstance.maxSize 4096

def cZeroSumTruncateCLM (s : Finset I) : JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZeroSum 𝕜 E :=
  ∑ i ∈ s, (JLMS.CZeroSum.singleIsometry (𝕜 := 𝕜) (E := E) i).toContinuousLinearMap.comp
    (JLMS.CZeroSum.evalCLM i)

theorem cZeroSumTruncateCLM_apply (s : Finset I) (x : JLMS.CZeroSum 𝕜 E) :
    cZeroSumTruncateCLM s x = JLMS.CZeroSum.truncate s x := by
  rw [JLMS.CZeroSum.truncate_eq_sum_single]
  simp only [cZeroSumTruncateCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    JLMS.CZeroSum.singleIsometry_apply, JLMS.CZeroSum.evalCLM_apply]

theorem cZeroSumTruncateCLM_sup (s : Finset I) (x y : JLMS.CZeroSum 𝕜 E) :
    ‖cZeroSumTruncateCLM (𝕜 := 𝕜) (E := E) s x +
      (ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E) -
        cZeroSumTruncateCLM (𝕜 := 𝕜) (E := E) s) y‖ ≤
      max ‖x‖ ‖y‖ := by
  classical
  apply JLMS.CZeroSum.norm_le (le_trans (norm_nonneg x) (le_max_left _ _))
  intro i
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    cZeroSumTruncateCLM_apply, JLMS.CZeroSum.add_apply, JLMS.CZeroSum.sub_apply,
    JLMS.CZeroSum.truncate_apply]
  by_cases hi : i ∈ s
  · simpa only [if_pos hi, sub_self, add_zero] using
      (JLMS.CZeroSum.norm_apply_le_norm x i).trans (le_max_left _ _)
  · simpa only [if_neg hi, sub_zero, zero_add] using
      (JLMS.CZeroSum.norm_apply_le_norm y i).trans (le_max_right _ _)

theorem cZeroSumTruncateCLM_szlenkBound {κ : Ordinal} (hκpos : 1 ≤ κ)
    (hκ : ∀ a < κ, ∀ b < κ, a ♯ b < κ)
    (hE : ∀ i, OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 (E i)) κ) (s : Finset I) :
    OperatorSzlenkBound (cZeroSumTruncateCLM (𝕜 := 𝕜) (E := E) s) κ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [cZeroSumTruncateCLM, Finset.sum_empty] using operatorSzlenkBound_zero hκpos
  | @insert i s hi ih =>
      rw [cZeroSumTruncateCLM, Finset.sum_insert hi]
      apply OperatorSzlenkBound.add hκ _ ih
      simpa only [ContinuousLinearMap.id_comp] using
        (hE i).comp (JLMS.CZeroSum.evalCLM i)
          (JLMS.CZeroSum.singleIsometry (𝕜 := 𝕜) (E := E) i).toContinuousLinearMap

theorem cZeroSum_szlenkBound {κ : Ordinal} (hκpos : 1 ≤ κ)
    (hκ : ∀ a < κ, ∀ b < κ, a ♯ b < κ)
    (hE : ∀ i, OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 (E i)) κ) :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E))
      (κ * Ordinal.omega0) := by
  apply operatorSzlenkBound_of_sup_projections (l := atTop)
    (cZeroSumTruncateCLM (𝕜 := 𝕜) (E := E))
  · intro x
    simpa only [cZeroSumTruncateCLM_apply] using JLMS.CZeroSum.tendsto_truncate x
  · exact cZeroSumTruncateCLM_sup (𝕜 := 𝕜) (E := E)
  · exact cZeroSumTruncateCLM_szlenkBound hκpos hκ hE

theorem cZeroSum_szlenkBound_omega0_sq
    (hE : ∀ i, OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 (E i))
      (Ordinal.omega0 : Ordinal.{0})) :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 E))
      (Ordinal.omega0 ^ (2 : Ordinal.{0})) := by
  simpa only [show (2 : Ordinal.{0}) = 1 + 1 by norm_num,
    Ordinal.opow_add, Ordinal.opow_one] using cZeroSum_szlenkBound Ordinal.one_lt_omega0.le
    (fun a ha b hb => nadd_lt_omega0 ha hb) hE

end Posets
