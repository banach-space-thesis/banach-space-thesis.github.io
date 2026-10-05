import ThesisCommon.Analysis.RieszKantorovich
import ThesisCommon.Analysis.L1Lattice

/-! The actual modulus and regularity of all bounded real L¹ operators.
This discharges the real L¹ instance of the regularity background used in
PEMS Section 3. The absolute-kernel identification is a separate theorem. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def lOneOperatorModulus (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  operatorModulus (lOne_norm_add_of_nonneg μ) (lOne_norm_add_of_nonneg ν) T

theorem lOneOperatorModulus_nonneg (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (f : Lp ℝ 1 μ) (hf : 0 ≤ f) : 0 ≤ lOneOperatorModulus T f :=
  operatorModulus_nonneg _ _ T f hf

theorem lOneOperatorModulus_dominates (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (f : Lp ℝ 1 μ) : |T f| ≤ lOneOperatorModulus T |f| :=
  abs_apply_le_operatorModulus_abs _ _ T f

theorem lOneOperatorModulus_least (T R : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hR : ∀ f : Lp ℝ 1 μ, 0 ≤ f → |T f| ≤ R f) (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    lOneOperatorModulus T f ≤ R f :=
  operatorModulus_least _ _ T R hR f hf

theorem norm_lOneOperatorModulus (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ‖lOneOperatorModulus T‖ = ‖T‖ := norm_operatorModulus _ _ T

theorem lOneOperatorModulus_rieszKantorovich (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    IsLUB (T '' Set.Icc (-f) f) (lOneOperatorModulus T f) :=
  operatorModulus_rieszKantorovich _ _ T f hf

theorem lOne_operator_regular (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃ P Q : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, (∀ f, 0 ≤ f → 0 ≤ P f) ∧
      (∀ f, 0 ≤ f → 0 ≤ Q f) ∧ T = P - Q :=
  exists_positive_operator_decomposition (lOne_norm_add_of_nonneg μ) (lOne_norm_add_of_nonneg ν) T

end ThesisCommon
