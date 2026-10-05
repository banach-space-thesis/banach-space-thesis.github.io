import Posets.CZeroMatrixOperators
import PosetsCommon.CZeroSumExt

/-! The operator-valued matrix construction in Lemma 6.17. -/
noncomputable section
set_option maxHeartbeats 1500000
open Filter Topology ThesisCommon
open scoped ENNReal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [Nonempty P]
  {X : P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  [∀ p, CompleteSpace (X p)]
  (ι : ∀ s t, X s →L[𝕜] X t)
  (hι : ∀ s t x, ‖ι s t x‖ ≤ ‖x‖)
  (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)

def blockMatrixValue (x : DependentCZeroSum 𝕜 X) (s : P) : X s :=
  ∑' t, M s t • ι t s (x.val t)

omit [Nonempty P] [∀ p, CompleteSpace (X p)] in
include hι in
theorem blockMatrix_term_bound (x : DependentCZeroSum 𝕜 X) (s t : P) :
    ‖M s t • ι t s (x.val t)‖ ≤ ‖M s t‖ * ‖x‖ := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    ((hι t s _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero x.val t)) (norm_nonneg _)

omit [Nonempty P] in
include hι hM in
theorem blockMatrix_summable (x : DependentCZeroSum 𝕜 X) (s : P) :
    Summable (fun t => M s t • ι t s (x.val t)) :=
  ((hM.1 s).mul_right ‖x‖).of_norm_bounded (blockMatrix_term_bound ι hι M x s)

omit [Nonempty P] [∀ p, CompleteSpace (X p)] in
include hι hM in
theorem blockMatrixValue_bound (x : DependentCZeroSum 𝕜 X) (s : P) :
    ‖blockMatrixValue ι M x s‖ ≤ rowNorm M * ‖x‖ := by
  calc
    ‖blockMatrixValue ι M x s‖ ≤ ∑' t, ‖M s t‖ * ‖x‖ :=
      tsum_of_norm_bounded ((hM.1 s).mul_right ‖x‖).hasSum
        (blockMatrix_term_bound ι hι M x s)
    _ = (∑' t, ‖M s t‖) * ‖x‖ := tsum_mul_right
    _ ≤ rowNorm M * ‖x‖ := mul_le_mul_of_nonneg_right
      (le_ciSup (rowNorm_bdd M hM) s) (norm_nonneg _)

def blockMatrixToLP : DependentCZeroSum 𝕜 X →L[𝕜] lp X ∞ :=
  ({toFun := fun x => ⟨blockMatrixValue ι M x, memℓp_infty
      ⟨rowNorm M * ‖x‖, by rintro _ ⟨s, rfl⟩; exact blockMatrixValue_bound ι hι M hM x s⟩⟩
    map_add' := by
      intro x y
      apply lp.ext
      funext s
      change (∑' t, M s t • ι t s (x.val t + y.val t)) =
        (∑' t, M s t • ι t s (x.val t)) + ∑' t, M s t • ι t s (y.val t)
      simp_rw [map_add, smul_add]
      exact (blockMatrix_summable ι hι M hM x s).tsum_add
        (blockMatrix_summable ι hι M hM y s)
    map_smul' := by
      intro a x
      apply lp.ext
      funext s
      change (∑' t, M s t • ι t s (a • x.val t)) =
        a • ∑' t, M s t • ι t s (x.val t)
      simp_rw [map_smul, smul_comm (M s _) a]
      exact (blockMatrix_summable ι hι M hM x s).tsum_const_smul a} : DependentCZeroSum 𝕜 X →ₗ[𝕜] lp X ∞).mkContinuous
    (rowNorm M) (fun x => lp.norm_le_of_forall_le
      (mul_nonneg (rowNorm_nonneg M hM) (norm_nonneg x)) (blockMatrixValue_bound ι hι M hM x))

theorem blockMatrixToLP_injection (t s : P) (x : X t) :
    blockMatrixToLP ι hι M hM (sumInjection 𝕜 X t x) s = M s t • ι t s x := by
  classical
  change (∑' r, M s r • ι r s ((sumInjection 𝕜 X t x).val r)) = _
  rw [tsum_eq_single t]
  · simp [sumInjection]
  · intro r hr
    simp [sumInjection, Pi.single_eq_of_ne hr]

theorem blockMatrixToLP_injection_mem (hcols : ZeroColumnsOn 𝕜 M) (t : P) (x : X t) :
    blockMatrixToLP ι hι M hM (sumInjection 𝕜 X t x) ∈ cZeroSumSubmodule 𝕜 X := by
  change Tendsto (fun s => ‖blockMatrixToLP ι hι M hM (sumInjection 𝕜 X t x) s‖) cofinite (𝓝 0)
  simp_rw [blockMatrixToLP_injection]
  apply squeeze_zero (fun s => norm_nonneg _) (fun s => ?_)
    (by simpa using (hcols t).norm.mul_const ‖x‖)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hι t s x) (norm_nonneg _)

theorem blockMatrixToLP_mem (hcols : ZeroColumnsOn 𝕜 M) (x : DependentCZeroSum 𝕜 X) :
    blockMatrixToLP ι hι M hM x ∈ cZeroSumSubmodule 𝕜 X := by
  apply (cZeroSum_isClosed 𝕜 X).mem_of_tendsto
    ((blockMatrixToLP ι hι M hM).continuous.continuousAt.tendsto.comp
      (finiteProjection_tendsto 𝕜 X x))
  apply Eventually.of_forall
  intro F
  simp only [Function.comp_apply, finiteProjection, ContinuousLinearMap.sum_apply, map_sum,
    ContinuousLinearMap.comp_apply]
  exact Submodule.sum_mem _ (fun t ht => blockMatrixToLP_injection_mem ι hι M hM hcols t _)

def blockMatrixLift (hcols : ZeroColumnsOn 𝕜 M) : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X :=
  (blockMatrixToLP ι hι M hM).codRestrict (cZeroSumSubmodule 𝕜 X)
    (blockMatrixToLP_mem ι hι M hM hcols)

theorem blockMatrixLift_apply (hcols : ZeroColumnsOn 𝕜 M) (x : DependentCZeroSum 𝕜 X) (s : P) :
    (blockMatrixLift ι hι M hM hcols x).val s = ∑' t, M s t • ι t s (x.val t) := rfl

theorem blockMatrixLift_block (hcols : ZeroColumnsOn 𝕜 M) (s t : P) :
    operatorBlock 𝕜 X X (blockMatrixLift ι hι M hM hcols) s t = M s t • ι t s := by
  apply ContinuousLinearMap.ext
  intro x
  exact blockMatrixToLP_injection ι hι M hM t s x

theorem blockMatrixLift_norm_le (hcols : ZeroColumnsOn 𝕜 M) :
    ‖blockMatrixLift ι hι M hM hcols‖ ≤ rowNorm M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (rowNorm_nonneg M hM)
  intro x
  exact lp.norm_le_of_forall_le (mul_nonneg (rowNorm_nonneg M hM) (norm_nonneg x))
    (blockMatrixValue_bound ι hι M hM x)

end Posets
