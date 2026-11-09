import BanachIsometric.CanonicalHemisphereCone
import BanachIsometric.SignedFacetVertexMatrix
import BanachIsometric.SuspensionConeProduct

/-! Coordinates of the actual affine hemisphere cone. Their first axis is
the north pole and their tail uses exactly the chosen equator isometry.
The actual vertex determinant has the alternating face sign times the
signed pole direction. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric Matrix NormedSpace
open scoped Topology

private def prependLinearEquiv (d : ℕ) :
    (ℝ × (Fin d → ℝ)) ≃ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun p := Fin.cons p.1 p.2
  invFun u := (u 0, fun j => u j.succ)
  left_inv _ := rfl
  right_inv _ := funext fun j => Fin.cases rfl (fun _ => rfl) j
  map_add' _ _ := funext fun j => Fin.cases rfl (fun _ => rfl) j
  map_smul' _ _ := funext fun j => Fin.cases rfl (fun _ => rfl) j

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def canonicalHemisphereChartCoordinates (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) : V ≃L[ℝ] (Fin (n + 3) → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv (((equatorSplit v).toLinearEquiv.trans
    ((LinearEquiv.refl ℝ ℝ).prodCongr
      ((equatorStandardLinearIsometry v (n + 1) hdim).toLinearEquiv.trans
        (EuclideanSpace.equiv (Fin (n + 2)) ℝ).toLinearEquiv))).trans
    (prependLinearEquiv (n + 2)))

theorem canonicalHemisphereChartCoordinates_combination (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (a : ℝ) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    canonicalHemisphereChartCoordinates v n hdim (a • v.val + equatorCenteredLinear v n hdim y) =
      Fin.cons a (fun j => y j) := by
  let L := equatorStandardLinearIsometry v (n + 1) hdim
  let x := a • v.val + equatorCenteredLinear v n hdim y
  have hx' : (equatorSplit v).symm (a, L.symm y) = x := equatorSplit_symm_apply v _
  have hx : equatorSplit v x = (a, L.symm y) := by
    rw [← hx', ContinuousLinearEquiv.apply_symm_apply]
  change Fin.cons (α := fun _ : Fin (n + 3) => ℝ)
    (equatorSplit v x).1 (fun j => L (equatorSplit v x).2 j) = _
  rw [hx, L.apply_symm_apply]

theorem canonicalHemisphereFacet_vertexMatrix (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (ε : ℝ) (hPole : pole.val = ε • v.val) (i : Fin (n + 3)) :
    Matrix.of (fun row col => canonicalHemisphereChartCoordinates v n hdim
      (canonicalHemisphereFacetVertices v pole n hdim i col) row) =
      signedHemisphereVertexMatrix (n + 1) ε i := by
  have hHead : canonicalHemisphereChartCoordinates v n hdim pole.val =
      Fin.cons ε (0 : Fin (n + 2) → ℝ) := by
    simpa only [hPole, map_zero, add_zero] using
      canonicalHemisphereChartCoordinates_combination v n hdim ε 0
  have hTail (j : Fin (n + 2)) : canonicalHemisphereChartCoordinates v n hdim
      (centeredEquatorFacetVertices v n hdim i j) =
      Fin.cons 0 (fun k => centeredSimplexVertices n (i.succAbove j) k) := by
    simpa only [zero_smul, zero_add, centeredEquatorFacetVertices, Function.comp_apply, centeredEquatorVertices] using
      canonicalHemisphereChartCoordinates_combination v n hdim 0 (centeredSimplexVertices n (i.succAbove j))
  ext row col
  refine Fin.cases ?_ (fun j => ?_) col
  · simp only [Matrix.of_apply, canonicalHemisphereFacetVertices, Fin.cons_zero, hHead]
    exact Fin.cases rfl (fun _ => rfl) row
  · simp only [Matrix.of_apply, canonicalHemisphereFacetVertices, Fin.cons_succ, hTail]
    exact Fin.cases rfl (fun _ => rfl) row

theorem canonicalHemisphereFacet_vertexMatrix_det (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (ε : ℝ) (hPole : pole.val = ε • v.val) (i : Fin (n + 3)) :
    (Matrix.of (fun row col => canonicalHemisphereChartCoordinates v n hdim
      (canonicalHemisphereFacetVertices v pole n hdim i col) row)).det =
      ε * (Int.negOnePow (i.val : ℤ) • signedFacetCenter (n + 1)) := by
  rw [canonicalHemisphereFacet_vertexMatrix v pole n hdim ε hPole i, signedHemisphereVertexMatrix_det]

theorem canonicalHemisphereFacet_affine_coordinates (v pole : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (ε : ℝ) (hPole : pole.val = ε • v.val)
    (i : Fin (n + 3)) (w : Simplex (n + 2)) :
    canonicalHemisphereChartCoordinates v n hdim
      (affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) w) =
      (signedHemisphereVertexMatrix (n + 1) ε i).mulVec w.val := by
  let e := canonicalHemisphereChartCoordinates v n hdim
  rw [← canonicalHemisphereFacet_vertexMatrix v pole n hdim ε hPole i]
  change e (∑ j : Fin (n + 3), w j • canonicalHemisphereFacetVertices v pole n hdim i j) = _
  simp only [map_sum, map_smul]
  funext row
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm]
  apply Finset.sum_congr rfl
  intro j _
  rfl

theorem canonicalHemisphereFacet_ray_coordinates (v pole : sphere (0 : V) 1)
    (hSide : pole = v ∨ pole = -v) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (ε : ℝ) (hPole : pole.val = ε • v.val) (i : Fin (n + 3)) (w : Simplex (n + 2)) (r : ℝ) :
    canonicalHemisphereChartCoordinates v n hdim (r • (canonicalHemisphereFacet v pole n hdim i w).val.val) =
      (r * ‖affineSingularSimplex (canonicalHemisphereFacetVertices v pole n hdim i) w‖⁻¹) •
        (signedHemisphereVertexMatrix (n + 1) ε i).mulVec w.val := by
  rw [canonicalHemisphereFacet_val v pole hSide, NormedSpace.normalize, smul_smul, map_smul,
    canonicalHemisphereFacet_affine_coordinates v pole n hdim ε hPole]

end BanachIsometric.SingularPrism
