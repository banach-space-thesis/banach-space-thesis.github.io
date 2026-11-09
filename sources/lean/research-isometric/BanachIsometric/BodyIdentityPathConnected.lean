import BanachIsometric.OperatorBodyLieGroup
import BanachIsometric.IdentityComponentProperties
import BanachIsometric.PathConnectedZeroHomology
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! The ACTUAL connected identity component of the original operator-unit
body group is path-connected. The already constructed atlas gives local
path-connectedness in its original topology; the actual open identity
component inherits it, and its proved connectedness finishes the argument.
Its actual degree-zero rational singular homology is consequently ℚ.
No compact-group homotopy torsion or rational Hurewicz premise is used. -/

noncomputable section
namespace BanachIsometric

open Set MeasureTheory
open scoped Topology Matrix.Norms.Operator

theorem locPathConnectedSpace_bodyAutomorphismGroup_of_interior {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    LocPathConnectedSpace (bodyAutomorphismGroup S) := by
  obtain ⟨e, _he, I, c, _hLie, _hcompact⟩ :=
    exists_compact_analytic_bodyAutomorphismGroup_of_interior μ S hS hreg h0
  letI := c
  exact ChartedSpace.locPathConnectedSpace
    (H := bodyStabilizerLieModel (coordinateMeasure μ) (coordinateBody (e '' S)) I)
    (M := bodyAutomorphismGroup S)

theorem pathConnectedSpace_bodyIdentityComponent_of_interior {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    PathConnectedSpace (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) := by
  letI := locPathConnectedSpace_bodyAutomorphismGroup_of_interior μ S hS hreg h0
  have hopen : IsOpen ((Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) :
      Set (bodyAutomorphismGroup S)) :=
    isOpen_bodyAutomorphismGroup_connectedComponent_of_interior μ S hS hreg h0
  letI := hopen.locPathConnectedSpace
  letI := connectedSpace_connectedComponentOfOne (bodyAutomorphismGroup S)
  exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance

def bodyIdentityComponentZeroHomologyEquiv {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    SingularPrism.RawZeroHomology (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S))
      ≃ₗ[ℚ] ℚ := by
  letI := pathConnectedSpace_bodyIdentityComponent_of_interior μ S hS hreg h0
  exact SingularPrism.rawZeroHomologyPathConnectedEquiv 1

end BanachIsometric
