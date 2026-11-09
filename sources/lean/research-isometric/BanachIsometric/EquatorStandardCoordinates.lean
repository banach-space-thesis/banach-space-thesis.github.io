import BanachIsometric.EquatorCoordinates
import BanachIsometric.SphereGenerator

/-! The actual equator in an arbitrary finite-dimensional real inner product
space has the required standard metric-sphere model. The coordinate change is
induced by a genuine linear isometry, so neither norm nor scalar action is
replaced. -/

noncomputable section
namespace BanachIsometric
open Set Metric

def sphereHomeomorphOfLinearIsometryEquiv
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ V] [NormedSpace ℝ W] (e : V ≃ₗᵢ[ℝ] W) :
    sphere (0 : V) 1 ≃ₜ sphere (0 : W) 1 where
  toFun x := ⟨e x.val, by
    rw [mem_sphere, dist_zero_right, e.norm_map]
    exact norm_eq_of_mem_sphere x⟩
  invFun x := ⟨e.symm x.val, by
    rw [mem_sphere, dist_zero_right, e.symm.norm_map]
    exact norm_eq_of_mem_sphere x⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.val
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem nonempty_equatorSphere_homeomorph_standard
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 2) :
    Nonempty (EquatorSphere v ≃ₜ SphereGenerator.Sph n) := by
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
  exact ⟨sphereHomeomorphOfLinearIsometryEquiv b.repr⟩

end BanachIsometric
