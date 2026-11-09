import BanachIsometric.CanonicalHemisphereOrientation
import BanachIsometric.ExactFamilyCoordinates

/-! The ordered hemisphere chart becomes a linear isometry when its
coordinate vector is interpreted in the genuine Euclidean norm. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def canonicalHemisphereIsometricCoordinates (v : sphere (0 : F) 1) (n : ℕ)
    (hdim : Module.finrank ℝ F = n + 3) : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 3)) := by
  let e := canonicalHemisphereChartCoordinates v n hdim
  let E := EuclideanSpace.equiv (Fin (n + 3)) ℝ
  let L := equatorStandardLinearIsometry v (n + 1) hdim
  refine ⟨(e.trans E.symm).toLinearEquiv, ?_⟩
  intro x
  obtain ⟨⟨a, w⟩, rfl⟩ := (equatorSplit v).symm.surjective x
  rw [equatorSplit_symm_apply]
  change ‖E.symm (e (a • v.val + (w : F)))‖ = ‖a • v.val + (w : F)‖
  have hW : (w : F) = equatorCenteredLinear v n hdim (L w) := by
    change (w : F) = (L.symm (L w) : F)
    rw [L.symm_apply_apply]
  have he : e (a • v.val + (w : F)) = Fin.cons a (fun j => L w j) := by
    conv_lhs => rw [hW]
    exact canonicalHemisphereChartCoordinates_combination v n hdim a (L w)
  rw [he]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [equator_normal_norm_sq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  change ‖a‖ ^ 2 + ∑ j : Fin (n + 2), ‖L w j‖ ^ 2 = _
  rw [← EuclideanSpace.norm_sq_eq, L.norm_map, Real.norm_eq_abs, sq_abs]

@[simp] theorem canonicalHemisphereIsometricCoordinates_coordinate (v : sphere (0 : F) 1) (n : ℕ)
    (hdim : Module.finrank ℝ F = n + 3) (x : F) :
    (EuclideanSpace.equiv (Fin (n + 3)) ℝ) (canonicalHemisphereIsometricCoordinates v n hdim x) =
      canonicalHemisphereChartCoordinates v n hdim x :=
  (EuclideanSpace.equiv (Fin (n + 3)) ℝ).apply_symm_apply _

@[simp] theorem canonicalHemisphereIsometricCoordinates_symm_coordinate (v : sphere (0 : F) 1) (n : ℕ)
    (hdim : Module.finrank ℝ F = n + 3) (x : Fin (n + 3) → ℝ) :
    (canonicalHemisphereIsometricCoordinates v n hdim).symm ((EuclideanSpace.equiv (Fin (n + 3)) ℝ).symm x) =
      (canonicalHemisphereChartCoordinates v n hdim).symm x := by
  change (canonicalHemisphereChartCoordinates v n hdim).symm
    ((EuclideanSpace.equiv (Fin (n + 3)) ℝ) ((EuclideanSpace.equiv (Fin (n + 3)) ℝ).symm x)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

end BanachIsometric.SingularPrism
