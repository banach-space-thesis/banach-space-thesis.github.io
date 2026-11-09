import BanachIsometric.ExactFamilyTopology
import BanachIsometric.ComplexHyperplaneRepresentation

/-!
# Actual real isometric coordinates for tangential exact families

The normal sphere map and every section operator are transported explicitly.
Lipschitz regularity, tangency and the original gauge identity are proved for
the transported maps. In the complex application this changes coordinates
only, retaining the original complex action on the Hermitian ambient space.
-/

namespace BanachIsometric

open scoped NNReal Topology

noncomputable section

section SphereCoordinates

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def linearIsometry_unitSphereMap (e : W ≃ₗᵢ[ℝ] V) :
    C(Metric.sphere (0 : W) 1, Metric.sphere (0 : V) 1) where
  toFun (z : Metric.sphere (0 : W) 1) := ⟨e z.val, by
    rw [Metric.mem_sphere, dist_zero_right, e.norm_map]
    simpa only [Metric.mem_sphere, dist_zero_right] using z.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.continuous.comp
      (continuous_subtype_val : Continuous (fun z : Metric.sphere (0 : W) 1 => z.val))

theorem linearIsometry_unitSphereMap_isometry (e : W ≃ₗᵢ[ℝ] V) :
    Isometry (linearIsometry_unitSphereMap e) := by
  intro z w
  change edist (e z.val) (e w.val) = edist z.val w.val
  exact e.edist_map _ _

end SphereCoordinates

namespace ExactTangentialFamily

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {g : V → ℝ} {p : E → ℝ}

/-- Isometric ambient coordinate transport of the actual operator family. -/
def transportAmbient (A : ExactTangentialFamily E V g p) (e : W ≃ₗᵢ[ℝ] V) :
    ExactTangentialFamily E W (fun w => g (e w)) p where
  normal := (linearIsometry_unitSphereMap e.symm).comp
    (A.normal.comp (linearIsometry_unitSphereMap e))
  maps z := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.maps (linearIsometry_unitSphereMap e z))
  maps_lipschitz := by
    obtain ⟨L, hL⟩ := A.maps_lipschitz
    let T : (E →L[ℝ] V) →L[ℝ] (E →L[ℝ] W) :=
      ContinuousLinearMap.compL ℝ E V W e.symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact ⟨_, T.lipschitz.comp
      (hL.comp (linearIsometry_unitSphereMap_isometry e).lipschitz)⟩
  tangent := by
    intro z y
    change inner ℝ (e.symm (A.maps (linearIsometry_unitSphereMap e z) y))
      (e.symm ((A.normal (linearIsometry_unitSphereMap e z)).val)) = 0
    rw [e.symm.inner_map_map]
    exact A.tangent _ y
  gauge_eq := by
    intro z y
    change g (e (e.symm (A.maps (linearIsometry_unitSphereMap e z) y))) = p y
    rw [e.apply_symm_apply]
    exact A.gauge_eq _ y

@[simp]
theorem transportAmbient_maps_apply (A : ExactTangentialFamily E V g p)
    (e : W ≃ₗᵢ[ℝ] V) (z : Metric.sphere (0 : W) 1) (y : E) :
    (A.transportAmbient e).maps z y =
      e.symm (A.maps (linearIsometry_unitSphereMap e z) y) := rfl

@[simp]
theorem transportAmbient_normal_apply (A : ExactTangentialFamily E V g p)
    (e : W ≃ₗᵢ[ℝ] V) (z : Metric.sphere (0 : W) 1) :
    ((A.transportAmbient e).normal z).val =
      e.symm ((A.normal (linearIsometry_unitSphereMap e z)).val) := rfl

/-- The concrete complex hyperplane argument can therefore feed an ordinary
real Euclidean Jacobian calculation in real dimension `2*(n+1)`. -/
def complexRealCoordinates {n : ℕ} {g : ComplexHermitianAmbient n → ℝ}
    (A : ExactTangentialFamily E (ComplexHermitianAmbient n) g p) :
    ExactTangentialFamily E (EuclideanSpace ℝ (Fin (2 * (n + 1))))
      (fun w => g (complexHermitianAmbient_realCoordinates n w)) p :=
  A.transportAmbient (complexHermitianAmbient_realCoordinates n)

end ExactTangentialFamily

end

end BanachIsometric
