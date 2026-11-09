import BanachIsometric.SphereNormalProjection
import BanachIsometric.ExactSectionBundleConstruction

/-! The real hyperplane bundle from the original Lipschitz normal field:
actual real rank and projection regularity are conclusions. -/

namespace BanachIsometric

open Set MeasureTheory
open scoped NNReal

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem normalHyperplane_finrank {m : ℕ} (hDim : Module.finrank ℝ F = m + 1)
    (u : Metric.sphere (0 : F) 1) : Module.finrank ℝ (normalHyperplane u) = m := by
  letI : Fact (Module.finrank ℝ F = m + 1) := ⟨hDim⟩
  apply Submodule.finrank_orthogonal_span_singleton
  intro hu
  have hn : ‖u.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  simp only [hu, norm_zero, zero_ne_one] at hn

theorem nonempty_realHyperplanePrincipalData {P : Type*} [PseudoMetricSpace P] {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    {p : F → ℝ} (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (normal : P → Metric.sphere (0 : F) 1) {L : ℝ≥0} (hNormal : LipschitzWith L normal)
    (hDim : Module.finrank ℝ F = m + 1) (a₀ : P)
    (hequiv : ∀ a, RealSectionEquivalent p (normalHyperplane (normal a₀)) (normalHyperplane (normal a))) :
    Nonempty (ExactSectionPrincipalData m p (fun a => normalHyperplane (normal a)) a₀) := by
  apply nonempty_exactSectionPrincipalData μ hp hSphere _
    (lipschitzWith_normalHyperplane_family normal hNormal) _ a₀ hequiv
  intro a
  rw [normalHyperplane_finrank hDim]
  simp

end
end BanachIsometric
