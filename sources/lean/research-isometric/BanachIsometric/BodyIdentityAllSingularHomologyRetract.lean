import BanachIsometric.BodyIdentitySingularHomologyRetract
import BanachIsometric.RawZeroSingularHomology

/-! One actual finite-polyhedron domination gives split maps on the actual
concrete rational singular homology in degree zero and every positive degree.
No finite-dimensionality or simplicial-to-singular comparison is assumed. -/

noncomputable section
namespace BanachIsometric

open Set MeasureTheory SingularPrism
open scoped Topology

theorem bodyIdentityComponent_actual_singular_homology_retract_all_degrees {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ n : ℕ, ∃ K : FiniteNerve.Complex (Fin n),
      ∃ f : C(Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S), K.space),
      ∃ g : C(K.space, Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)),
        (rawZeroHomologyMap g).comp (rawZeroHomologyMap f) = LinearMap.id ∧
        ∀ q : ℕ, (rawHomologyMap g q).comp (rawHomologyMap f q) = LinearMap.id := by
  obtain ⟨n, K, f, g, ⟨H⟩⟩ := bodyIdentityComponent_finite_polyhedron_domination μ S hS hreg h0
  refine ⟨n, K, f, g, ?_, fun q => rawHomology_retract_identity f g H q⟩
  rw [← rawZeroHomologyMap_comp, rawZeroHomologyMap_homotopy H, rawZeroHomologyMap_id]

end BanachIsometric
