import BanachIsometric.SimplexBoundaryCoordinates
import BanachIsometric.SphereGaugeLevelHomeomorph

/-! The explicit radial boundary-simplex parametrization is an actual
homeomorphism onto the original Euclidean sphere. Its restriction to each
face is exactly the singular simplex used by `CanonicalSphereCycle`, with
no change of norm and no extra boundary extension. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open SphereGenerator NormedSpace

def simplexBoundarySphereHomeomorph (n : ℕ) : SimplexBoundary n ≃ₜ Sph (n + 1) :=
  (simplexBoundaryGaugeLevelHomeomorph n).trans
    (sphereGaugeLevelHomeomorph (simplexGauge_homogeneous n)
      (simplexGauge_continuous n)).symm

@[simp] theorem simplexBoundarySphereHomeomorph_apply_val (n : ℕ)
    (w : SimplexBoundary n) :
    (simplexBoundarySphereHomeomorph n w).val =
      normalize (centeredSimplexVector n w.val) := by
  exact sphereGaugeLevelHomeomorph_symm_apply_val
    (simplexGauge_homogeneous n) (simplexGauge_continuous n)
    (simplexBoundaryToGaugeLevel n w)

def boundarySimplexFaceInclusion (n : ℕ) (i : Fin (n + 3)) :
    C(Simplex (n + 1), SimplexBoundary n) where
  toFun w := ⟨face i w, ⟨i, simplex_face_missing i w⟩⟩
  continuous_toFun := (face i).continuous.subtype_mk _

theorem simplexBoundarySphereHomeomorph_face (n : ℕ) (i : Fin (n + 3)) :
    (⟨simplexBoundarySphereHomeomorph n,
      (simplexBoundarySphereHomeomorph n).continuous⟩ : C(SimplexBoundary n, Sph (n + 1))).comp
      (boundarySimplexFaceInclusion n i) = boundarySimplexSphereFace n i := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  exact simplexBoundarySphereHomeomorph_apply_val n (boundarySimplexFaceInclusion n i w)

end BanachIsometric.SingularPrism
