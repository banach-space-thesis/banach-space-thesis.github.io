import ThesisCommon.Analysis.ContinuousMapRieszControl
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Removal of the diagonal atom and a local quantitative residual bound. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {K 𝕜 : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [RCLike 𝕜]

theorem continuousMap_integral_split_singleton (ν : Measure K) [IsFiniteMeasure ν]
    (f : C(K, 𝕜)) (t : K) :
    ∫ x, f x ∂ν = (ν.real {t} : 𝕜) * f t + ∫ x in {t}ᶜ, f x ∂ν := by
  have h := integral_add_compl (measurableSet_singleton t)
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f) (μ := ν))
  rw [integral_singleton, RCLike.real_smul_eq_coe_mul] at h
  exact h.symm

theorem continuousMapRiesz_residual_formula (μ : C(K, 𝕜) →L[𝕜] 𝕜)
    (f : C(K, 𝕜)) (t : K) :
    μ f - continuousMapRieszVector μ {t} * f t =
      ((∫ x in {t}ᶜ, f x ∂continuousMapRieszPositive (continuousMapFunctionalRe μ)) -
        (∫ x in {t}ᶜ, f x ∂continuousMapRieszNegative (continuousMapFunctionalRe μ))) +
      (((∫ x in {t}ᶜ, f x ∂continuousMapRieszPositive (continuousMapFunctionalIm μ)) -
        (∫ x in {t}ᶜ, f x ∂continuousMapRieszNegative (continuousMapFunctionalIm μ)))) * RCLike.I := by
  rw [continuousMap_complex_riesz_representation, continuousMapRieszVector_apply,
    continuousMapRieszSigned_apply _ (measurableSet_singleton t),
    continuousMapRieszSigned_apply _ (measurableSet_singleton t)]
  rw [continuousMap_integral_split_singleton
      (continuousMapRieszPositive (continuousMapFunctionalRe μ)) f t,
    continuousMap_integral_split_singleton
      (continuousMapRieszNegative (continuousMapFunctionalRe μ)) f t,
    continuousMap_integral_split_singleton
      (continuousMapRieszPositive (continuousMapFunctionalIm μ)) f t,
    continuousMap_integral_split_singleton
      (continuousMapRieszNegative (continuousMapFunctionalIm μ)) f t]
  simp only [RCLike.ofReal_sub]
  ring

theorem continuousMap_setIntegral_localize (ν : Measure K) (f : C(K, 𝕜))
    (t : K) (A : Set K) (hA : ∀ x ∉ A, f x = 0) :
    ∫ x in {t}ᶜ, f x ∂ν = ∫ x in A \ {t}, f x ∂ν := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_singleton t).compl
    (fun _ hx => hx.2)
  intro x hx
  apply hA x
  intro hxa
  exact hx.2 ⟨hxa, hx.1⟩

theorem norm_four_integrals_le_control (μ : C(K, 𝕜) →L[𝕜] 𝕜)
    (f : C(K, 𝕜)) (A : Set K) :
    ‖((∫ x in A, f x ∂continuousMapRieszPositive (continuousMapFunctionalRe μ)) -
        (∫ x in A, f x ∂continuousMapRieszNegative (continuousMapFunctionalRe μ))) +
      (((∫ x in A, f x ∂continuousMapRieszPositive (continuousMapFunctionalIm μ)) -
        (∫ x in A, f x ∂continuousMapRieszNegative (continuousMapFunctionalIm μ)))) * RCLike.I‖ ≤
      ‖f‖ * (continuousMapRieszControl μ).real A := by
  have bound (ν : Measure K) [IsFiniteMeasure ν] :
      ‖∫ x in A, f x ∂ν‖ ≤ ‖f‖ * ν.real A :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (fun x _ => f.norm_coe_le_norm x)
  have him : ‖((∫ x in A, f x ∂continuousMapRieszPositive (continuousMapFunctionalIm μ)) -
        (∫ x in A, f x ∂continuousMapRieszNegative (continuousMapFunctionalIm μ))) * (RCLike.I : 𝕜)‖ ≤
      ‖(∫ x in A, f x ∂continuousMapRieszPositive (continuousMapFunctionalIm μ)) -
        (∫ x in A, f x ∂continuousMapRieszNegative (continuousMapFunctionalIm μ))‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (rclike_norm_I_le_one (𝕜 := 𝕜))
  have hnorm := (norm_add_le
    ((∫ x in A, f x ∂continuousMapRieszPositive (continuousMapFunctionalRe μ)) -
      (∫ x in A, f x ∂continuousMapRieszNegative (continuousMapFunctionalRe μ)))
    (((∫ x in A, f x ∂continuousMapRieszPositive (continuousMapFunctionalIm μ)) -
      (∫ x in A, f x ∂continuousMapRieszNegative (continuousMapFunctionalIm μ))) * RCLike.I)).trans
    (add_le_add (norm_sub_le _ _) (him.trans (norm_sub_le _ _)))
  refine hnorm.trans ?_
  have hfour := add_le_add (add_le_add (bound (continuousMapRieszPositive (continuousMapFunctionalRe μ)))
    (bound (continuousMapRieszNegative (continuousMapFunctionalRe μ))))
    (add_le_add (bound (continuousMapRieszPositive (continuousMapFunctionalIm μ)))
      (bound (continuousMapRieszNegative (continuousMapFunctionalIm μ))))
  apply hfour.trans_eq
  unfold continuousMapRieszControl
  rw [measureReal_add_apply, measureReal_add_apply, measureReal_add_apply]
  ring

theorem continuousMapRiesz_residual_local_bound (μ : C(K, 𝕜) →L[𝕜] 𝕜)
    (f : C(K, 𝕜)) (t : K) (A : Set K) (hA : ∀ x ∉ A, f x = 0) :
    ‖μ f - continuousMapRieszVector μ {t} * f t‖ ≤
      ‖f‖ * (continuousMapRieszControl μ).real (A \ {t}) := by
  rw [continuousMapRiesz_residual_formula]
  simp_rw [continuousMap_setIntegral_localize _ f t A hA]
  exact norm_four_integrals_le_control μ f (A \ {t})

end ThesisCommon
