import BanachIsometric.EquatorStandardCoordinates

/-! Explicit equator coordinates retain the underlying genuine linear
isometry. Applications needing actual differential or norm transport should
use this map, rather than choosing an arbitrary homeomorphism of spheres. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def equatorStandardLinearIsometry (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 2) : (ℝ ∙ v.val)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) := by
  have hv : v.val ≠ 0 := by
    intro hz
    have h := norm_eq_of_mem_sphere v
    rw [hz, norm_zero] at h
    norm_num at h
  letI : Fact (Module.finrank ℝ V = (n + 1) + 1) := ⟨by omega⟩
  have horth : Module.finrank ℝ (ℝ ∙ v.val)ᗮ = n + 1 :=
    Submodule.finrank_orthogonal_span_singleton hv
  let b : OrthonormalBasis (Fin (n + 1)) ℝ (ℝ ∙ v.val)ᗮ :=
    (stdOrthonormalBasis ℝ (ℝ ∙ v.val)ᗮ).reindex (finCongr horth)
  exact b.repr

def equatorStandardSphereHomeomorph (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 2) : EquatorSphere v ≃ₜ SphereGenerator.Sph n :=
  sphereHomeomorphOfLinearIsometryEquiv (equatorStandardLinearIsometry v n hdim)

theorem equatorStandardSphereHomeomorph_isometry (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 2) : Isometry (equatorStandardSphereHomeomorph v n hdim) :=
  fun x y => (equatorStandardLinearIsometry v n hdim).isometry x.val y.val

theorem equatorStandardSphereHomeomorph_symm_isometry (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 2) : Isometry (equatorStandardSphereHomeomorph v n hdim).symm :=
  fun x y => (equatorStandardLinearIsometry v n hdim).symm.isometry x.val y.val

end BanachIsometric
