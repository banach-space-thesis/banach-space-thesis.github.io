import BanachIsometric.SphereRepetitionConeGerms
import BanachIsometric.ChartSemiconjugacyDerivative
import BanachIsometric.RegularBranches

/-! A negatively oriented genuine chart on either side of a positive strip
map proves a positive derivative of the represented repetition map. -/

namespace BanachIsometric.SphereGenerator

open Filter
open scoped Topology unitInterval

noncomputable section

theorem repetitionCone_derivative_of_chart (n d : ℕ) (ρ a ε : ℝ)
    (hρ : 0 < ρ) (ha : a ≠ 1 / 2) (haxis : (2 * a - 1) ^ 2 < 1)
    (T : PiolaSpace (n + 2) → PiolaSpace (n + 2))
    (B : PiolaSpace (n + 2) →L[ℝ] PiolaSpace (n + 2))
    (hT : HasFDerivAt T B (stripChart n ε (cubeSphereConeAxis n ρ a)))
    (hB : B.det < 0)
    (heq : ∀ᶠ z in 𝓝 (cubeSphereConeAxis n ρ a),
      sphereRepetitionCone n d (cubeSphereConeChart n z) = T (stripChart n ε z)) :
    DifferentiableAt ℝ (sphereRepetitionCone n d)
        (cubeSphereConeChart n (cubeSphereConeAxis n ρ a)) ∧
      0 < (fderiv ℝ (sphereRepetitionCone n d)
        (cubeSphereConeChart n (cubeSphereConeAxis n ρ a))).det := by
  let C := fderiv ℝ (cubeSphereConeChart n) (cubeSphereConeAxis n ρ a)
  have hC : C.det < 0 := det_fderiv_cubeSphereConeChart_axis_neg n ρ a hρ ha haxis
  let A := regularLinearEquiv C (ne_of_lt hC)
  have hA : (A : PiolaSpace (n + 2) →L[ℝ] PiolaSpace (n + 2)) = C :=
    regularLinearEquiv_coe C (ne_of_lt hC)
  have hS : HasStrictFDerivAt (cubeSphereConeChart n)
      (A : PiolaSpace (n + 2) →L[ℝ] PiolaSpace (n + 2)) (cubeSphereConeAxis n ρ a) := by
    rw [hA]
    exact hasStrictFDerivAt_cubeSphereConeChart_axis n ρ a ha haxis
  have hL := hasFDerivAt_stripChart n ε (cubeSphereConeAxis n ρ a)
  refine ⟨(hasFDerivAt_of_chart_semiconjugacy hS hT hL heq).differentiableAt, ?_⟩
  apply det_fderiv_pos_of_negative_chart_semiconjugacy hS hT hL heq
  · simpa only [hA] using hC
  · exact hB
  · rw [det_stripChartLinear]
    norm_num

end
end BanachIsometric.SphereGenerator
