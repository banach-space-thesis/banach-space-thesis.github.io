import BanachIsometric.BodyIdentityComponentFiniteDomination
import BanachIsometric.NativeSingularPrism

/-! Literal finite-polyhedron domination induces split maps on the actual
categorical rational singular homology in every degree. Finite-dimensional
singular homology of the finite polyhedron is not assumed or concluded. -/

noncomputable section
namespace BanachIsometric

open CategoryTheory Set MeasureTheory
open scoped Topology

theorem bodyIdentityComponent_native_singular_homology_retract {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ n : ℕ, ∃ K : FiniteNerve.Complex (Fin n),
      ∃ f : C(Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S), K.space),
      ∃ g : C(K.space, Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)),
        ∀ q : ℕ, (rationalSingularHomologyFunctor q).map (TopCat.ofHom f) ≫
          (rationalSingularHomologyFunctor q).map (TopCat.ofHom g) = 𝟙 _ := by
  obtain ⟨n, K, f, g, ⟨H⟩⟩ := bodyIdentityComponent_finite_polyhedron_domination μ S hS hreg h0
  refine ⟨n, K, f, g, fun q => ?_⟩
  calc
    _ = (rationalSingularHomologyFunctor q).map (TopCat.ofHom (g.comp f)) :=
      ((rationalSingularHomologyFunctor q).map_comp (TopCat.ofHom f) (TopCat.ofHom g)).symm
    _ = (rationalSingularHomologyFunctor q).map (𝟙 _) :=
      rationalSingularHomologyMap_homotopy H q
    _ = 𝟙 _ := (rationalSingularHomologyFunctor q).map_id _

end BanachIsometric
