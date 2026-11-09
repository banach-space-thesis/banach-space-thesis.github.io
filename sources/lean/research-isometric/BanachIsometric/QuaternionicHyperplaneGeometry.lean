import BanachIsometric.QuaternionicHyperplaneRegularity
import BanachIsometric.QuaternionicPairCoverage

/-! The actual quaternionic hyperplane field supplies the real geometry
needed by the exact-section principal bundle. Scalar and real ranks, tangent
containment, projection regularity, and pair coverage are proved. -/

namespace BanachIsometric.Quaternionic

open Set MeasureTheory
open scoped Quaternion NNReal

noncomputable section

abbrev HermitianAmbient (n : ℕ) := Euclidean (n + 1)

def hyperplaneField (n : ℕ) (u : Metric.sphere (0 : HermitianAmbient n) 1) :
    Submodule ℝ (HermitianAmbient n) := realNormalHyperplane (n + 1) u.val

theorem hyperplaneField_finrank (n : ℕ) (u : Metric.sphere (0 : HermitianAmbient n) 1) :
    Module.finrank ℝ (hyperplaneField n u) = 4 * n :=
  realNormalHyperplane_finrank n u.val
    (by simpa only [Metric.mem_sphere, dist_zero_right] using u.property)

theorem hyperplaneField_projection_lipschitz (n : ℕ) :
    LipschitzWith 8 (fun u : Metric.sphere (0 : HermitianAmbient n) 1 => (hyperplaneField n u).starProjection) :=
  realNormalHyperplane_projection_lipschitz (n + 1)

theorem hyperplaneField_le_real_perp (n : ℕ) (u : Metric.sphere (0 : HermitianAmbient n) 1) :
    hyperplaneField n u ≤ (ℝ ∙ u.val)ᗮ := realNormalHyperplane_le_perp (n + 1) u.val

theorem hyperplaneField_pair_coverage (n : ℕ) (hn : 2 ≤ n) (x y : HermitianAmbient n) :
    ∃ u : Metric.sphere (0 : HermitianAmbient n) 1, x ∈ hyperplaneField n u ∧ y ∈ hyperplaneField n u := by
  obtain ⟨u, hu, hux, huy⟩ := exists_unit_standardHermitian_annihilating_pair (n + 1) (by omega) x y
  exact ⟨⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩,
    (mem_realNormalHyperplane (n + 1) u x).mpr hux,
    (mem_realNormalHyperplane (n + 1) u y).mpr huy⟩

theorem nonempty_hyperplane_exactSectionPrincipalData (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin (4 * n)))) [μ.IsAddHaarMeasure]
    {p : HermitianAmbient n → ℝ} (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (Metric.sphere (0 : HermitianAmbient n) 1))
    (u₀ : Metric.sphere (0 : HermitianAmbient n) 1)
    (hequiv : ∀ u, RealSectionEquivalent p (hyperplaneField n u₀) (hyperplaneField n u)) :
    Nonempty (ExactSectionPrincipalData (4 * n) p (hyperplaneField n) u₀) := by
  exact nonempty_exactSectionPrincipalData μ hp hSphere (hyperplaneField n)
    (hyperplaneField_projection_lipschitz n)
    (fun u => by simpa only [finrank_euclideanSpace_fin] using hyperplaneField_finrank n u)
    u₀ hequiv

end
end BanachIsometric.Quaternionic
