import BanachIsometric.GaugeLevelGeometry
import BanachIsometric.RadialHomeomorphismLipschitz
import BanachIsometric.SignedSimplexMomentScaling

/-! The actual scaled radial map sends the round sphere into a null gauge
shell and recovers an evaluated vector whose gauge is the scale. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric MeasureTheory NormedSpace
open scoped NNReal Topology

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}

def scaledGaugeSphereMap (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g) (q : ℝ) :
    C(sphere (0 : EuclideanSpace ℝ (Fin n)) 1, Fin n → ℝ) := by
  have hRadial : Continuous (radialGaugeMap g) := by
    obtain ⟨ε, _, hε, _, hbound⟩ := hg.exists_norm_comparison hcont.continuousOn
    exact continuous_radialGaugeMap hg hcont hε (fun x => (hbound x).1)
  exact ⟨fun u => (EuclideanSpace.equiv (Fin n) ℝ) (q • radialGaugeMap g u.val),
    (EuclideanSpace.equiv (Fin n) ℝ).continuous.comp
      ((hRadial.comp continuous_subtype_val).const_smul q)⟩

theorem scaledGaugeSphereMap_apply (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    (q : ℝ) (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    scaledGaugeSphereMap hg hcont q u =
      (EuclideanSpace.equiv (Fin n) ℝ) (q • radialGaugeMap g u.val) := rfl

theorem exists_lipschitz_scaledGaugeSphereMap (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) {C : ℝ≥0} (hC : LipschitzOnWith C g (sphere 0 1)) (q : ℝ) :
    ∃ L : ℝ≥0, LipschitzWith L (scaledGaugeSphereMap hg hcont q) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_radialGaugeMap hg hC
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ) :=
    q • (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap
  have he : (scaledGaugeSphereMap hg hcont q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → _) =
      fun u => T (radialGaugeMap g u.val) := by
    funext u
    exact (EuclideanSpace.equiv (Fin n) ℝ).map_smul q _
  rw [he]
  exact ⟨_, T.lipschitz.comp (hK.comp (LipschitzWith.subtype_val _))⟩

theorem measure_range_scaledGaugeSphereMap_eq_zero (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure]
    (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g) {q : ℝ} (hq : 0 < q) :
    μ (range (scaledGaugeSphereMap hg hcont q)) = 0 := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let p := g ∘ e.symm
  have hp : IsDefinitePositiveHomogeneous p := by
    refine ⟨fun x => hg.nonneg (e.symm x), fun x => (hg.eq_zero_iff (e.symm x)).trans e.symm.map_eq_zero_iff, ?_⟩
    intro r hr x
    change g (e.symm (r • x)) = r * g (e.symm x)
    rw [e.symm.map_smul, hg.smul_nonneg _ hr]
  have hpc : Continuous p := hcont.comp e.symm.continuous
  have hnull := measure_frontier_pos_sublevel_eq_zero μ hp hpc hq
  rw [hp.frontier_pos_sublevel_eq_level hpc hq] at hnull
  refine measure_mono_null ?_ hnull
  rintro _ ⟨u, rfl⟩
  change g (e.symm (e (q • radialGaugeMap g u.val))) = q
  rw [e.symm_apply_apply, hg.smul_nonneg _ hq.le, gauge_radialGaugeMap hg, norm_eq_of_mem_sphere u, mul_one]

theorem scaledGaugeSphereMap_comp_scale (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g) (q : ℝ) :
    (continuousLinearSingularMap (simplexScalarMap n q)).comp (scaledGaugeSphereMap hg hcont 1) =
      scaledGaugeSphereMap hg hcont q := by
  apply ContinuousMap.ext
  intro u
  rw [ContinuousMap.comp_apply, scaledGaugeSphereMap_apply, scaledGaugeSphereMap_apply]
  simp [continuousLinearSingularMap, simplexScalarMap]

theorem gauge_smul_radialGaugeMap_normalize (hg : IsDefinitePositiveHomogeneous g)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) :
    g v • radialGaugeMap g (NormedSpace.normalize v) = v := by
  have hn := norm_pos_iff.mpr hv
  have hp := hg.pos hv
  rw [radialGaugeMap, norm_normalize hv, NormedSpace.normalize, hg.smul_nonneg _ (inv_nonneg.mpr hn.le),
    smul_smul, smul_smul]
  have h : g v * (1 / (‖v‖⁻¹ * g v)) * ‖v‖⁻¹ = 1 := by field_simp [hn.ne', hp.ne']
  rw [h, one_smul]

end BanachIsometric.SingularPrism
