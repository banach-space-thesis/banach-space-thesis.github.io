import ThesisCommon.Analysis.JamesBlockKernel
import ThesisCommon.Analysis.JamesRightShift

/-! Every sampling kernel is complementably embedded in an actual lp sum of
finite James intervals. A single zero coordinate is inserted first, so the
block decomposition requires no assumption on the first sampling index. -/
noncomputable section
open scoped ENNReal
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace ThesisCommon
private theorem retraction_before_equiv
    {𝕜 K L F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    [NormedAddCommGroup L] [NormedSpace 𝕜 L]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (J : K →L[𝕜] L) (Q : L →L[𝕜] K) (E : F ≃L[𝕜] L)
    (h : Q.comp J = ContinuousLinearMap.id 𝕜 K) :
    (Q.comp E.toContinuousLinearMap).comp (E.symm.toContinuousLinearMap.comp J) =
      ContinuousLinearMap.id 𝕜 K := by
  ext x
  change Q (E (E.symm (J x))) = x
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact DFunLike.congr_fun h x

variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (α : ℕ → ℕ) (hα : StrictMono α)

def jamesSamplingEndpoints : ℕ → ℕ
  | 0 => 0
  | n + 1 => α n + 1

@[simp] theorem jamesSamplingEndpoints_zero : jamesSamplingEndpoints α 0 = 0 := rfl

@[simp] theorem jamesSamplingEndpoints_succ (n : ℕ) :
    jamesSamplingEndpoints α (n + 1) = α n + 1 := rfl

include hα in
theorem jamesSamplingEndpoints_strict : StrictMono (jamesSamplingEndpoints α) := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => simp [jamesSamplingEndpoints]
  | succ n => exact Nat.add_lt_add_right (hα (Nat.lt_succ_self n)) 1

def jamesSamplingKernelShift :
    LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp α hα).toLinearMap →L[𝕜]
      LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp (jamesSamplingEndpoints α)
        (jamesSamplingEndpoints_strict α hα)).toLinearMap :=
  ((jamesRightShift (𝕜 := 𝕜) p hp 1).comp
    (LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp α hα).toLinearMap).subtypeL).codRestrict _ (by
      intro x
      apply (jamesSample_mem_ker_iff (𝕜 := 𝕜) p hp (jamesSamplingEndpoints α)
        (jamesSamplingEndpoints_strict α hα) _).mpr
      intro n
      change jamesRightShift (𝕜 := 𝕜) p hp 1 x.val (jamesSamplingEndpoints α n) = 0
      cases n with
      | zero => rw [jamesSamplingEndpoints_zero, jamesRightShift_apply, if_pos (by omega)]
      | succ n =>
        rw [jamesSamplingEndpoints_succ, jamesRightShift_apply,
          if_neg (by omega), Nat.add_sub_cancel]
        exact (jamesSample_mem_ker_iff (𝕜 := 𝕜) p hp α hα x.val).mp x.property n)

def jamesSamplingKernelDrop :
    LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp (jamesSamplingEndpoints α)
      (jamesSamplingEndpoints_strict α hα)).toLinearMap →L[𝕜]
      LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp α hα).toLinearMap :=
  ((jamesDrop (𝕜 := 𝕜) p hp 1).comp
    (LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp (jamesSamplingEndpoints α)
      (jamesSamplingEndpoints_strict α hα)).toLinearMap).subtypeL).codRestrict _ (by
      intro x
      apply (jamesSample_mem_ker_iff (𝕜 := 𝕜) p hp α hα _).mpr
      intro n
      change jamesDrop (𝕜 := 𝕜) p hp 1 x.val (α n) = 0
      rw [jamesDrop_apply]
      exact (jamesSample_mem_ker_iff (𝕜 := 𝕜) p hp (jamesSamplingEndpoints α)
        (jamesSamplingEndpoints_strict α hα) x.val).mp x.property (n + 1))

theorem jamesSamplingKernelDrop_comp_shift :
    (jamesSamplingKernelDrop (𝕜 := 𝕜) p hp α hα).comp
      (jamesSamplingKernelShift (𝕜 := 𝕜) p hp α hα) = ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (jamesDrop_rightShift (𝕜 := 𝕜) p hp 1) x.val

def jamesSamplingKernelBlockInsert :
    LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp α hα).toLinearMap →L[𝕜]
      JamesBlockSum (𝕜 := 𝕜) p (jamesSamplingEndpoints α) :=
  (jamesBlockKernelEquiv (𝕜 := 𝕜) p hp (jamesSamplingEndpoints α)
    (jamesSamplingEndpoints_strict α hα) rfl).symm.toContinuousLinearMap.comp
      (jamesSamplingKernelShift (𝕜 := 𝕜) p hp α hα)

def jamesSamplingKernelBlockRead :
    JamesBlockSum (𝕜 := 𝕜) p (jamesSamplingEndpoints α) →L[𝕜]
      LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp α hα).toLinearMap :=
  (jamesSamplingKernelDrop (𝕜 := 𝕜) p hp α hα).comp
    (jamesBlockKernelEquiv (𝕜 := 𝕜) p hp (jamesSamplingEndpoints α)
      (jamesSamplingEndpoints_strict α hα) rfl).toContinuousLinearMap

theorem jamesSamplingKernelBlockRead_comp_insert :
    (jamesSamplingKernelBlockRead (𝕜 := 𝕜) p hp α hα).comp
      (jamesSamplingKernelBlockInsert (𝕜 := 𝕜) p hp α hα) = ContinuousLinearMap.id 𝕜 _ := by
  exact retraction_before_equiv
    (jamesSamplingKernelShift (𝕜 := 𝕜) p hp α hα)
    (jamesSamplingKernelDrop (𝕜 := 𝕜) p hp α hα)
    (jamesBlockKernelEquiv (𝕜 := 𝕜) p hp (jamesSamplingEndpoints α)
      (jamesSamplingEndpoints_strict α hα) rfl)
    (jamesSamplingKernelDrop_comp_shift (𝕜 := 𝕜) p hp α hα)

end ThesisCommon
