import BanachIsometric.CircledRadialBallGauge

/-! Circledness of all finite scalar sections is exactly sufficient for
circledness of the original centered ball: each vector is treated in its
actual one-dimensional scalar span. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped Pointwise

noncomputable section

variable {R X : Type*} [NormedDivisionRing R] [NormedAlgebra ℝ R]
    [AddCommGroup X] [Module R X] [Module ℝ X] [IsScalarTower ℝ R X] [MetricSpace X]

omit [NormedAlgebra ℝ R] [Module ℝ X] [IsScalarTower ℝ R X] [MetricSpace X] in
theorem scalarCircled_of_finiteScalarSections {s : Set X}
    (h : ∀ Y : Submodule R X, FiniteDimensional R Y → Y ≠ ⊥ →
      ScalarCircled (R := R) (Y.subtype ⁻¹' s)) : ScalarCircled (R := R) s := by
  intro a ha
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hx₀ : x = 0
    · simpa only [hx₀, smul_zero] using hx
    · let Y : Submodule R X := R ∙ x
      have hY : Y ≠ ⊥ := Submodule.span_singleton_eq_bot.not.mpr hx₀
      let xY : Y := ⟨x, Submodule.mem_span_singleton_self x⟩
      have hxY : xY ∈ Y.subtype ⁻¹' s := hx
      have hax : a • xY ∈ a • (Y.subtype ⁻¹' s) := smul_mem_smul_set hxY
      rw [h Y inferInstance hY a ha] at hax
      exact hax
  · intro hy
    by_cases hy₀ : y = 0
    · exact ⟨y, hy, by change a • y = y; rw [hy₀, smul_zero]⟩
    · let Y : Submodule R X := R ∙ y
      have hY : Y ≠ ⊥ := Submodule.span_singleton_eq_bot.not.mpr hy₀
      let yY : Y := ⟨y, Submodule.mem_span_singleton_self y⟩
      have hyY : yY ∈ Y.subtype ⁻¹' s := hy
      rw [← h Y inferInstance hY a ha] at hyY
      obtain ⟨z, hz, haz⟩ := hyY
      exact ⟨z.val, hz, congrArg Subtype.val haz⟩

end
end BanachIsometric.MetricGeometry


