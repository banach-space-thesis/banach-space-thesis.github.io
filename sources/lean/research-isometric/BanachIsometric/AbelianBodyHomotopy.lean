import BanachIsometric.AbelianStabilizerHomotopy
import BanachIsometric.BodyIdentityComponentTransport

/-! An actual compact regular body with abelian identity automorphism
component has trivial actual higher homotopy groups. Covariance position,
finite moments and all group/homotopy equivalences are constructed, rather
than supplied as extra hypotheses. -/

noncomputable section
namespace BanachIsometric

open Set MeasureTheory
open scoped Topology Topology.Homotopy Matrix.Norms.Operator

theorem subsingleton_higherHomotopy_bodyIdentityComponent_of_abelian {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S)
    (hAbelian : ∀ R T : Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S), R * T = T * R)
    (n : ℕ) : Subsingleton (HomotopyGroup (Fin (n + 2))
      (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1) := by
  obtain ⟨e, _he, I, f, hf, hi⟩ :=
    exists_bodyAutomorphism_tensorStabilizer_equiv_of_interior μ S hS hreg h0
  let g := identityComponentMulEquiv f hf hi
  have hComm : ∀ R T : Subgroup.connectedComponentOfOne
      (unitaryRepresentationStabilizer (tensorTupleLinearRepresentation m I)
        (bodyTensorTuple (coordinateMeasure μ) (coordinateBody (e '' S)) I)), R * T = T * R := by
    intro R T
    obtain ⟨r, rfl⟩ := g.surjective R
    obtain ⟨t, rfl⟩ := g.surjective T
    rw [← g.map_mul, ← g.map_mul, hAbelian r t]
  letI := StabilizerLieCoordinates.subsingleton_higherHomotopy_of_abelian_identityComponent
    (tensorTupleLinearRepresentation m I)
    (bodyTensorTuple (coordinateMeasure μ) (coordinateBody (e '' S)) I)
    (contDiff_tensorTupleOrbit m I _) hComm n
  exact (identityComponentHomotopyEquiv (N := Fin (n + 2)) f hf hi).injective.subsingleton

theorem isOfFinOrder_higherHomotopy_bodyIdentityComponent_of_abelian {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S)
    (hAbelian : ∀ R T : Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S), R * T = T * R)
    (n : ℕ) (α : HomotopyGroup (Fin (n + 2))
      (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1) : IsOfFinOrder α := by
  letI := subsingleton_higherHomotopy_bodyIdentityComponent_of_abelian μ S hS hreg h0 hAbelian n
  have he : α = 1 := Subsingleton.elim _ _
  rw [he]
  exact IsOfFinOrder.one

end BanachIsometric
