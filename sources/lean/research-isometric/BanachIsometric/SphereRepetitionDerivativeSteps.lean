import BanachIsometric.SphereRepetitionChartDerivative

/-! Actual positive derivatives on the two literal affine strip branches. -/

namespace BanachIsometric.SphereGenerator

open scoped Topology unitInterval

noncomputable section

theorem cubeSphereConeAxis_tail_mem (n : ℕ) (ρ a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ i : Fin (n + 1), cubeSphereConeAxis n ρ a i.succ ∈ Set.Ioo (0 : ℝ) 1 := by
  intro i
  induction i using Fin.cases with
  | zero => exact ha
  | succ i => norm_num [cubeSphereConeAxis, cubeCoordinateAxis]

theorem sphereRepetitionCone_positive_right_step (n d : ℕ) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : 1 / 2 < a) (ha1 : a < 1) (hb : 2 * a - 1 ≠ 1 / 2) :
    DifferentiableAt ℝ (sphereRepetitionCone n (d + 1))
        (cubeSphereConeChart n (cubeSphereConeAxis n ρ a)) ∧
      0 < (fderiv ℝ (sphereRepetitionCone n (d + 1))
        (cubeSphereConeChart n (cubeSphereConeAxis n ρ a))).det := by
  have haxis : (2 * a - 1) ^ 2 < 1 := by nlinarith
  have htarget : (2 * (2 * a - 1) - 1) ^ 2 < 1 := by nlinarith
  have hT : HasFDerivAt (cubeSphereConeChart n)
      (fderiv ℝ (cubeSphereConeChart n) (cubeSphereConeAxis n ρ (2 * a - 1)))
      (stripChart n 1 (cubeSphereConeAxis n ρ a)) := by
    rw [stripChart_axis]
    exact (hasStrictFDerivAt_cubeSphereConeChart_axis n ρ _ hb htarget).hasFDerivAt
  apply repetitionCone_derivative_of_chart n (d + 1) ρ a 1 hρ (ne_of_gt ha) haxis
    (cubeSphereConeChart n) _ hT
  · exact det_fderiv_cubeSphereConeChart_axis_neg n ρ _ hρ hb htarget
  · exact sphereRepetitionCone_right_germ n d hρ
      (cubeSphereConeAxis_tail_mem n ρ a ⟨by linarith, ha1⟩) ha

theorem sphereRepetitionCone_positive_left_step (n d : ℕ) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha0 : 0 < a) (ha : a < 1 / 2) (hb : 2 * a ≠ 1 / 2)
    (hD : DifferentiableAt ℝ (sphereRepetitionCone n d)
      (cubeSphereConeChart n (cubeSphereConeAxis n ρ (2 * a))))
    (hpos : 0 < (fderiv ℝ (sphereRepetitionCone n d)
      (cubeSphereConeChart n (cubeSphereConeAxis n ρ (2 * a)))).det) :
    DifferentiableAt ℝ (sphereRepetitionCone n (d + 1))
        (cubeSphereConeChart n (cubeSphereConeAxis n ρ a)) ∧
      0 < (fderiv ℝ (sphereRepetitionCone n (d + 1))
        (cubeSphereConeChart n (cubeSphereConeAxis n ρ a))).det := by
  have haxis : (2 * a - 1) ^ 2 < 1 := by nlinarith
  have htarget : (2 * (2 * a) - 1) ^ 2 < 1 := by nlinarith
  let D := fderiv ℝ (sphereRepetitionCone n d)
    (cubeSphereConeChart n (cubeSphereConeAxis n ρ (2 * a)))
  let C := fderiv ℝ (cubeSphereConeChart n) (cubeSphereConeAxis n ρ (2 * a))
  have hC : HasFDerivAt (cubeSphereConeChart n) C (cubeSphereConeAxis n ρ (2 * a)) :=
    (hasStrictFDerivAt_cubeSphereConeChart_axis n ρ _ hb htarget).hasFDerivAt
  have hT : HasFDerivAt (fun z => sphereRepetitionCone n d (cubeSphereConeChart n z))
      (D.comp C) (stripChart n 0 (cubeSphereConeAxis n ρ a)) := by
    rw [stripChart_axis, sub_zero]
    exact hD.hasFDerivAt.comp _ hC
  apply repetitionCone_derivative_of_chart n (d + 1) ρ a 0 hρ (ne_of_lt ha) haxis
    (fun z => sphereRepetitionCone n d (cubeSphereConeChart n z)) (D.comp C) hT
  · change LinearMap.det (D.toLinearMap.comp C.toLinearMap) < 0
    rw [LinearMap.det_comp]
    exact mul_neg_of_pos_of_neg hpos
      (det_fderiv_cubeSphereConeChart_axis_neg n ρ _ hρ hb htarget)
  · exact sphereRepetitionCone_left_germ n d hρ
      (cubeSphereConeAxis_tail_mem n ρ a ⟨ha0, by linarith⟩) ha

end
end BanachIsometric.SphereGenerator
