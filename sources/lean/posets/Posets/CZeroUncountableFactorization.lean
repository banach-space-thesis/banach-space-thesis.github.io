import Posets.CZeroUncountableSelection
import Posets.CZeroUncountableMatrix
import Posets.OrdinalIdealTransportCofinalMaps
import Posets.CZeroContinuousAmplification
import ThesisCommon.Analysis.Primary

/-! A full uncountable scalar c₀ space factors through one of T and I−T.
Countable row/column supports allow an exact diagonal compression, with a
uniform factorisation bound of two. Singular cardinals are included. -/

noncomputable section
open Set Cardinal ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {I : Type}
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

local instance uncountableScalarGroup : NormedAddCommGroup (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) := inferInstance
local instance uncountableScalarSpace : NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) := inferInstance

theorem cZeroSum_insertCLM_single_scalar (e : I → I) (he : Function.Injective e)
    (j : I) (z : 𝕜) :
    cZeroSum_insertCLM (𝕜 := 𝕜) (E := fun _ : I => 𝕜) e he (JLMS.CZeroSum.single j z) =
      JLMS.CZeroSum.single (e j) z := by
  classical
  apply JLMS.CZeroSum.ext
  intro i
  by_cases hi : ∃ k, e k = i
  · obtain ⟨k, rfl⟩ := hi
    rw [cZeroSum_insertCLM_apply_selected]
    by_cases hk : k = j
    · subst k; simp
    · rw [JLMS.CZeroSum.single_apply_ne _ _ hk,
        JLMS.CZeroSum.single_apply_ne _ _ (fun h => hk (he h))]
  · have hij : i ≠ e j := fun h => hi ⟨j, h.symm⟩
    change cZeroSum_insertFun (E := fun _ : I => 𝕜) e (fun k => JLMS.CZeroSum.single (𝕜 := 𝕜)
      (E := fun _ : I => 𝕜) j z k) i = _
    simp only [cZeroSum_insertFun, dif_neg hi, JLMS.CZeroSum.single_apply_ne _ _ hij]

theorem cZeroSum_factorsIdentityWith_of_selected_matrix
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (e : I ↪ I) (hdiag : ∀ i, (1 : ℝ) / 2 ≤ ‖cZeroSumScalarMatrix T (e i) (e i)‖)
    (hoff : ∀ i j, i ≠ j → cZeroSumScalarMatrix T (e i) (e j) = 0) :
    FactorsIdentityWith T (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) 2 := by
  let a (i : I) := cZeroSumScalarMatrix T (e i) (e i)
  have hane (i : I) : a i ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hdiag i))
  have hinv (i : I) : ‖(a i)⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.mpr (hane i))]
    linarith [hdiag i]
  let q (i : I) : 𝕜 →L[𝕜] 𝕜 := (a i)⁻¹ • ContinuousLinearMap.id 𝕜 𝕜
  have hq (i : I) : ‖q i‖ ≤ 2 := by
    simpa only [q, norm_smul, ContinuousLinearMap.norm_id, mul_one] using hinv i
  let P : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) :=
    cZeroSum_insertCLM (𝕜 := 𝕜) (E := fun _ : I => 𝕜) e e.injective
  let Q : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) :=
    (JLMS.CZeroSum.mapCLM q (by norm_num : (0:ℝ) ≤ 2) hq).comp
      (JLMS.CZeroSum.comapCLM (𝕜 := 𝕜) (E := fun _ : I => 𝕜) e e.injective)
  have hP : ‖P‖ ≤ 1 := norm_cZeroSum_insertCLM_le e e.injective
  have hQ : ‖Q‖ ≤ 2 := by
    calc
      _ ≤ ‖JLMS.CZeroSum.mapCLM q (by norm_num : (0:ℝ) ≤ 2) hq‖ *
        ‖JLMS.CZeroSum.comapCLM (𝕜 := 𝕜) (E := fun _ : I => 𝕜) e e.injective‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (2 : ℝ) * 1 := mul_le_mul (JLMS.CZeroSum.norm_mapCLM_le _ _ _)
        (norm_cZeroSum_comapCLM_le e e.injective) (norm_nonneg _) (by norm_num)
      _ = 2 := mul_one _
  refine ⟨Q, P, ?_, (mul_le_mul hQ hP (norm_nonneg _) (by norm_num)).trans_eq (mul_one 2)⟩
  apply cZeroSum_clm_ext_columns
  intro j z
  apply JLMS.CZeroSum.ext
  intro i
  change (a i)⁻¹ * T (P (JLMS.CZeroSum.single j z)) (e i) =
    JLMS.CZeroSum.single (𝕜 := 𝕜) (E := fun _ : I => 𝕜) j z i
  rw [show P (JLMS.CZeroSum.single j z) = JLMS.CZeroSum.single (e j) z from
    cZeroSum_insertCLM_single_scalar e e.injective j z]
  rw [cZeroScalarSingle_smul (e j) z, map_smul, JLMS.CZeroSum.smul_apply]
  change (a i)⁻¹ * (z * cZeroSumScalarMatrix T (e i) (e j)) = _
  by_cases hij : i = j
  · subst j
    rw [JLMS.CZeroSum.single_apply_self]
    change (a i)⁻¹ * (z * a i) = z
    rw [mul_left_comm, inv_mul_cancel₀ (hane i), mul_one]
  · rw [hoff i j hij, mul_zero, mul_zero, JLMS.CZeroSum.single_apply_ne _ _ hij]

theorem cZeroSum_factorsIdentityWith_of_large_diagonal
    (hI : ℵ₀ < #I)
    (T : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))
    (S : Set I) (hS : #I ≤ #S) (hdiag : ∀ i ∈ S, (1 : ℝ) / 2 ≤ ‖cZeroSumScalarMatrix T i i‖) :
    FactorsIdentityWith T (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) 2 := by
  obtain ⟨e, heS, he⟩ := exists_uncountable_independent_embedding hI S hS
    (cZeroSumMatrixForbidden T) (cZeroSumMatrixForbidden_countable T)
    (cZeroSumMatrixForbidden_self T) (cZeroSumMatrixForbidden_symm T)
  apply cZeroSum_factorsIdentityWith_of_selected_matrix T e (fun i => hdiag _ (heS i))
  intro i j hij
  by_contra hn
  exact he i j hij (Or.inr hn)

theorem uncountableScalarCZero_hasCPFP_two (hI : ℵ₀ < #I) :
    HasCPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) 2 := by
  classical
  letI : Uncountable I := Cardinal.aleph0_lt_mk_iff.mp hI
  intro T
  let S : Set I := {i | (1 : ℝ) / 2 ≤ ‖cZeroSumScalarMatrix T i i‖}
  rcases infinite_twoColor_large I S with hS | hS
  · exact Or.inl (cZeroSum_factorsIdentityWith_of_large_diagonal hI T S hS (fun _ hi => hi))
  · right
    apply cZeroSum_factorsIdentityWith_of_large_diagonal hI
      (ContinuousLinearMap.id 𝕜 _ - T) Sᶜ hS
    intro i hi
    have hn : ¬ (1 : ℝ) / 2 ≤ ‖cZeroSumScalarMatrix T i i‖ := hi
    have hmatrix : cZeroSumScalarMatrix (ContinuousLinearMap.id 𝕜 _ - T) i i =
        1 - cZeroSumScalarMatrix T i i := by
      simp [cZeroSumScalarMatrix]
    rw [hmatrix]
    have hh := norm_add_le (cZeroSumScalarMatrix T i i) (1 - cZeroSumScalarMatrix T i i)
    rw [add_sub_cancel, norm_one] at hh
    linarith

end Posets
