import BanachIsometric.LipschitzOrthogonalHomotopy
import BanachIsometric.LipschitzIntervalInterpolation
import BanachIsometric.RawLipschitzPrism

/-! The orthogonal homotopy is jointly Lipschitz on a compact parameter
space. Its actual singular prism transports a finite cycle between the
normal and evaluated directions. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric NormedSpace
open scoped Topology NNReal unitInterval

variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [PseudoMetricSpace X] [CompactSpace X]

theorem exists_lipschitz_orthogonalSphereHomotopy
    (f g : C(X, sphere (0 : V) 1)) (hfg : ∀ x, inner ℝ (f x).val (g x).val = 0)
    {K L : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    ∃ M : ℝ≥0, LipschitzWith M (orthogonalSphereHomotopy f g hfg).toContinuousMap := by
  let s := sphere (0 : V) 1
  obtain ⟨M, hM⟩ := exists_lipschitz_unitInterval_interpolation (fun x => (f x).val) (fun x => (g x).val)
    ((LipschitzWith.subtype_val s).comp hf) ((LipschitzWith.subtype_val s).comp hg)
  have hlow (z : unitInterval × X) : (1 / 2 : ℝ) ≤
      ‖(1 - (z.1 : ℝ)) • (f z.2).val + (z.1 : ℝ) • (g z.2).val‖ :=
    norm_orthogonal_unit_affine_lower (norm_eq_of_mem_sphere (f z.2))
      (norm_eq_of_mem_sphere (g z.2)) (hfg z.2) z.1
  have hnorm := lipschitzWith_normalize_of_lower_bound hM (by norm_num : (0 : ℝ≥0) < 1 / 2)
    (fun z => by simpa using hlow z)
  exact ⟨_, hnorm.subtype_mk (fun z => (orthogonalSphereHomotopy f g hfg z).property)⟩

theorem exists_lipschitz_orthogonal_projection_filling (n : ℕ)
    (f g : C(X, sphere (0 : V) 1)) (hfg : ∀ x, inner ℝ (f x).val (g x).val = 0)
    {K L : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (c : RawRationalChains X (n + 1)) (hc : c ∈ rawLipschitzCarrier X (n + 1))
    (hcycle : rawBoundary n c = 0)
    (a : RawRationalChains (sphere (0 : V) 1) (n + 1))
    (b : RawRationalChains (sphere (0 : V) 1) (n + 2))
    (hb : b ∈ rawLipschitzCarrier (sphere (0 : V) 1) (n + 2))
    (hfill : rawBoundary (n + 1) b = rawChainMap g (n + 1) c - a) :
    ∃ z : RawRationalChains (sphere (0 : V) 1) (n + 2),
      z ∈ rawLipschitzCarrier (sphere (0 : V) 1) (n + 2) ∧
      rawBoundary (n + 1) z = rawChainMap f (n + 1) c - a := by
  let H := orthogonalSphereHomotopy f g hfg
  obtain ⟨M, hH⟩ := exists_lipschitz_orthogonalSphereHomotopy f g hfg hf hg
  have hPrismLip := rawPrism_preserves_lipschitz H hH (n + 1) hc
  have hP := LinearMap.congr_fun (rawPrism_chain_identity H n) c
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, hcycle, map_zero, add_zero] at hP
  refine ⟨b - rawPrism H (n + 1) c, (rawLipschitzCarrier _ _).sub_mem hb hPrismLip, ?_⟩
  rw [map_sub, hfill, hP]
  abel

end BanachIsometric.SingularPrism
