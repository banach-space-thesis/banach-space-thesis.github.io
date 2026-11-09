import BanachIsometric.RealEvenHyperplaneRigidity
import BanachIsometric.RealOddGeometricTorsion

/-! Actual even-dimensional central hyperplane sections of a literal radial
star carrier force an ellipsoid, without a topology or rigidity premise. -/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology NNReal

noncomputable section
theorem RadialStarBody.real_even_hyperplane_sections_quadratic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
    (K : RadialStarBody V) {C : ℝ≥0} (hK : LipschitzWith C K.radius)
    (k : ℕ) (hdim : Module.finrank ℝ V = 2 * k + 3)
    (hSections : ∀ E F : Submodule ℝ V,
      Module.finrank ℝ E = 2 * k + 2 → Module.finrank ℝ F = 2 * k + 2 →
      ∃ T : E ≃ₗ[ℝ] F, T '' (E.subtype ⁻¹' K.carrier) = F.subtype ⁻¹' K.carrier) :
    ∃ Q : QuadraticForm ℝ V, Q.PosDef ∧ (∀ x, Q x = K.gauge x ^ 2) ∧ K.carrier = {x | Q x ≤ 1} := by
  obtain ⟨L, hL⟩ := K.exists_gauge_sphere_lipschitz hK
  have hGauge : RealEquivalentRealSections (2 * k + 2) K.gauge := by
    intro E F hE hF
    obtain ⟨T, hT⟩ := hSections E F hE hF
    refine ⟨T, ?_⟩
    intro x
    have h := MetricGeometry.gauge_image_linearEquiv T (E.subtype ⁻¹' K.carrier) x
    rw [hT, MetricGeometry.gauge_preimage_submodule, MetricGeometry.gauge_preimage_submodule,
      K.gauge_eq_minkowski, K.gauge_eq_minkowski] at h
    exact h
  obtain ⟨Q, hQpos, hQ⟩ := real_even_hyperplane_quadratic
    k hdim K.gauge_homogeneous hL hGauge
  exact ⟨Q, hQpos, hQ, K.carrier_eq_sublevel.trans (gauge_sublevel_eq_quadratic_sublevel K.gauge_homogeneous.nonneg Q hQ)⟩

end
end BanachIsometric
