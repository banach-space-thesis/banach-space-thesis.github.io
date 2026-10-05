import ThesisCommon.Analysis.IntervalKernelOscillation
import ThesisCommon.Analysis.IntervalCZeroEquiv
import ThesisCommon.Analysis.IntervalLpAssembly
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! Explicit remaining inputs in LPCK's C[0,1] UPFP proof. The quantitative
Weis assertion below is an OPEN proposition specification, not an axiom or
a proved theorem. The conditional assembly uses the checked kernel/Baire
dichotomy and tracks the distortion of the fixed Milutin isomorphism. -/
noncomputable section
open Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev BinaryCantorSpace := ℕ → Bool
abbrev CantorContinuous (𝕜 : Type*) [RCLike 𝕜] := C(BinaryCantorSpace, 𝕜)

/-- OPEN: the quantitative continuous-factor assertion extracted in the
manuscript from Weis (1986), Theorem 2, with threshold fixed at one.
The constant is quantified outside the operator and the continuity point. -/
def IntervalWeisBound (𝕜 : Type*) [RCLike 𝕜] (C : ℝ) : Prop :=
  ∀ (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval),
    1 ≤ oscillation (intervalOperatorKernel T) t →
    ContinuousAt (oscillation (intervalOperatorKernel T)) t →
    FactorsIdentityWith T (CantorContinuous 𝕜) C

theorem interval_hasCPFP_of_weis_milutin {C : ℝ}
    (hWeis : IntervalWeisBound 𝕜 C)
    (e : CantorContinuous 𝕜 ≃L[𝕜] IntervalContinuous 𝕜) :
    HasCPFP 𝕜 (IntervalContinuous 𝕜)
      (C * (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖)) := by
  intro T
  rcases interval_kernel_oscillation_continuity_dichotomy T with hT | hT
  · obtain ⟨t, ht, hc⟩ := hT
    exact Or.inl ((hWeis T t ht hc).target_equiv e)
  · obtain ⟨t, ht, hc⟩ := hT
    exact Or.inr ((hWeis _ t ht hc).target_equiv e)

theorem interval_hasUPFP_of_weis_milutin {C : ℝ}
    (hWeis : IntervalWeisBound 𝕜 C)
    (e : CantorContinuous 𝕜 ≃L[𝕜] IntervalContinuous 𝕜) :
    HasUPFP 𝕜 (IntervalContinuous 𝕜) := by
  let d := C * (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖)
  refine ⟨max 1 d, le_max_left _ _, ?_⟩
  intro T
  rcases interval_hasCPFP_of_weis_milutin hWeis e T with h | h
  · exact Or.inl (h.mono (le_max_right _ _))
  · exact Or.inr (h.mono (le_max_right _ _))

theorem interval_primary_of_weis_milutin {C : ℝ}
    (hWeis : IntervalWeisBound 𝕜 C)
    (e : CantorContinuous 𝕜 ≃L[𝕜] IntervalContinuous 𝕜) :
    IsPrimary 𝕜 (IntervalContinuous 𝕜) :=
  (interval_hasUPFP_of_weis_milutin hWeis e).isPrimary_of_sequenceSelfSimilar
    interval_sequenceSelfSimilar

theorem interval_lp_upfp_primary_of_weis_milutin {C : ℝ}
    (hWeis : IntervalWeisBound 𝕜 C)
    (e : CantorContinuous 𝕜 ≃L[𝕜] IntervalContinuous 𝕜) (p : BanachExponent) :
    HasUPFP 𝕜 (SequenceSum p (IntervalContinuous 𝕜)) ∧
      IsPrimary 𝕜 (SequenceSum p (IntervalContinuous 𝕜)) :=
  interval_lp_upfp_primary (interval_hasUPFP_of_weis_milutin hWeis e) intervalCZeroEquiv p.val

end ThesisCommon
