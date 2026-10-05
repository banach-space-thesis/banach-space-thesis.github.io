import ThesisCommon.Analysis.L1AdjointOne
import ThesisCommon.Analysis.IntegralKernelTruncationModulus

/-! The adjoint-at-one representative of an integral operator is its
kernel column integral. The resulting essential-supremum formula for a
singular-plus-integral remainder uses the actual operator modulus and
the actual Banach adjoint. It requires finite input and s-finite output
measure, with no topology or countable-generation hypothesis. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]
variable {k : X × Y → ℝ} {K S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem IsIntegralKernel.integral_apply_eq_column (hk : IsIntegralKernel k K)
    (f : Lp ℝ 1 μ) :
    (∫ y, K f y ∂ν) = ∫ x, (∫ y, k (x, y) ∂ν) * f x ∂μ := by
  rw [integral_congr_ae (hk.represents f)]
  calc
    (∫ y, ∫ x, k (x, y) * f x ∂μ ∂ν) =
        ∫ x, ∫ y, k (x, y) * f x ∂ν ∂μ :=
      (integral_integral_swap (integrable_kernel_mul hk.measurable hk.hasKernelBound f)).symm
    _ = _ := by simp_rw [integral_mul_const]

theorem IsIntegralKernel.positiveAdjointOne_eq_column_ae
    (hk : IsIntegralKernel k K) (hK : 0 ≤ K) :
    positiveAdjointOne K hK =ᵐ[μ] fun x => ∫ y, k (x, y) ∂ν := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => ((Lp.memLp (positiveAdjointOne K hK)).integrable le_top).integrableOn)
    (fun A _ _ => hk.integrable.integral_prod_left.integrableOn)
  intro A hA _
  rw [← linftyL1Pairing_indicator (positiveAdjointOne K hK) A hA, positiveAdjointOne_pairing_apply,
    hk.integral_apply_eq_column]
  calc
    (∫ x, (∫ y, k (x, y) ∂ν) * lOneIndicator μ A hA x ∂μ) =
        ∫ x, A.indicator (fun x => ∫ y, k (x, y) ∂ν) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [lOneIndicator_coe (μ := μ) A hA] with x hx
      rw [hx]
      by_cases hxA : x ∈ A <;> simp [hxA]
    _ = _ := integral_indicator hA

theorem singular_integral_adjointOne_eq_column_ae
    (hk : IsIntegralKernel k K) :
    positiveAdjointOne (|S| + |K|) (add_nonneg (abs_nonneg S) (abs_nonneg K)) =ᵐ[μ]
      fun x => positiveAdjointOne |S| (abs_nonneg S) x + ∫ y, |k (x, y)| ∂ν := by
  rw [positiveAdjointOne_add |S| |K| (abs_nonneg S) (abs_nonneg K)]
  exact (Lp.coeFn_add _ _).trans ((hk.abs.positiveAdjointOne_eq_column_ae
    (abs_nonneg K)).mono fun x hx => by simp only [Pi.add_apply, hx])

theorem singular_integral_norm_eq_essSup_adjoint_column
    (hk : IsIntegralKernel k K) (hS : IsSingularOperator S) :
    ‖S + K‖ = essSup
      (fun x => positiveAdjointOne |S| (abs_nonneg S) x + ∫ y, |k (x, y)| ∂ν) μ := by
  rw [← norm_abs_lOneOperator, singular_integral_abs_add hS ⟨k, hk⟩]
  exact (norm_eq_essSup_positiveAdjointOne _ (add_nonneg (abs_nonneg S) (abs_nonneg K))).trans
    (essSup_congr_ae (singular_integral_adjointOne_eq_column_ae (S := S) hk))

theorem singular_truncated_norm_eq_essSup_adjoint_column
    (hk : IsIntegralKernel k K) (hS : IsSingularOperator S) (r : ℝ) :
    ‖S + hk.truncatedOperator r‖ = essSup
      (fun x => positiveAdjointOne |S| (abs_nonneg S) x +
        ∫ y, |truncatedKernel r k (x, y)| ∂ν) μ :=
  singular_integral_norm_eq_essSup_adjoint_column (hk.truncatedOperator_represents r) hS

end ThesisCommon
