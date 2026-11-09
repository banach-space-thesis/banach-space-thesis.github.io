import BanachIsometric.BodyComponentTransport
import Mathlib.Topology.Homotopy.Lifting

/-!
# Actual component groups and sections of covering maps

The connected identity component is a normal subgroup, and the actual body
component quotient has the discrete quotient topology. Covering sections are
constructed using Mathlib's proved homotopy lifting theorem. Sphere simple
connectivity and construction of the bundle's component covering are separate
inputs, not asserted here without proofs.
-/

noncomputable section

namespace BanachIsometric

open Set
open scoped Topology

theorem connectedComponentOfOne_normal (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (Subgroup.connectedComponentOfOne G).Normal := by
  constructor
  intro n hn g
  have hc : Continuous (fun x : G => g * x * g⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have h := hc.mapsTo_connectedComponent (1 : G) hn
  simpa using h

theorem discreteTopology_bodyAutomorphismGroup_components {m : ℕ}
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hC : covarianceOperator μ S = ContinuousLinearMap.id ℝ _)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    DiscreteTopology ((bodyAutomorphismGroup S) ⧸
      Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) :=
  Subgroup.discreteTopology _ (isOpen_bodyAutomorphismGroup_connectedComponent
    (μ := μ) (S := S) (hS := hS) (hC := hC) hreg h0)

/-- Any actual covering map has a continuous section over a simply connected,
locally path-connected base, after specifying one point in one fiber. -/
theorem exists_continuous_covering_section
    {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
    [SimplyConnectedSpace B] [LocPathConnectedSpace B]
    {p : E → B} (hp : IsCoveringMap p) (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀) :
    ∃ s : C(B, E), s b₀ = e₀ ∧ ∀ b, p (s b) = b := by
  obtain ⟨s, hs, _⟩ := hp.existsUnique_continuousMap_lifts
    (ContinuousMap.id B) b₀ e₀ he₀
  exact ⟨s, hs.1, fun b => congrFun hs.2 b⟩

end BanachIsometric
