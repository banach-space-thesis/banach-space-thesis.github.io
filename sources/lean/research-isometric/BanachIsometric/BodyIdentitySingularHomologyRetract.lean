import BanachIsometric.BodyIdentityComponentFiniteDomination
import BanachIsometric.RawSingularHomotopyInvariance

/-! The actual connected identity body group has its concrete rational
singular homology split into the actual singular homology of a genuine finite
polyhedron. The split identity follows from the constructed literal homotopy
and the proved actual prism theorem. This does not assume or assert the
remaining simplicial-to-singular finite-dimensionality comparison. -/

noncomputable section
namespace BanachIsometric

open Set MeasureTheory SingularPrism
open scoped Topology

theorem bodyIdentityComponent_actual_singular_homology_retract {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ n : ℕ, ∃ K : FiniteNerve.Complex (Fin n),
      ∃ f : C(Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S), K.space),
      ∃ g : C(K.space, Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)),
        ∀ q : ℕ, (rawHomologyMap g q).comp (rawHomologyMap f q) = LinearMap.id := by
  obtain ⟨n, K, f, g, ⟨H⟩⟩ := bodyIdentityComponent_finite_polyhedron_domination μ S hS hreg h0
  exact ⟨n, K, f, g, fun q => rawHomology_retract_identity f g H q⟩

end BanachIsometric
