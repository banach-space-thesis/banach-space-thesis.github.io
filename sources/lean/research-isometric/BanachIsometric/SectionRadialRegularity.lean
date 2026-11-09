import BanachIsometric.CovarianceNormalization
import BanachIsometric.LocalIsometricFrames
import BanachIsometric.StarBodyCompact

/-!
# Radial regularity of actual sections in moving isometric frames

The pulled-back section has gauge `p ∘ J` and radial function `1 / p(J θ)`.
Ambient sphere bounds give common inner and outer radii, while the operator
Lipschitz bound of the frames gives uniform parameter Lipschitz bounds for
those radii. These are the actual inputs to the covariance normalization.
-/

namespace BanachIsometric

open Set MeasureTheory
open scoped Topology NNReal

noncomputable section

section Reciprocal

variable {P : Type*} [PseudoMetricSpace P]

theorem lipschitzWith_reciprocal_of_positive_lower {f : P → ℝ} {C ε : ℝ≥0}
    (hC : LipschitzWith C f) (hε : 0 < ε) (hbound : ∀ a, (ε : ℝ) ≤ f a) :
    LipschitzWith (C / ε ^ 2) (fun a ↦ (f a)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hεr : 0 < (ε : ℝ) := hε
  have hfa : 0 < f a := hεr.trans_le (hbound a)
  have hfb : 0 < f b := hεr.trans_le (hbound b)
  have hprod : (ε : ℝ) ^ 2 ≤ f a * f b := by nlinarith [hbound a, hbound b]
  calc
    dist ((f a)⁻¹) ((f b)⁻¹) = dist (f a) (f b) / (f a * f b) := by
      rw [dist_inv_inv₀ hfa.ne' hfb.ne', Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hfa, abs_of_pos hfb]
    _ ≤ dist (f a) (f b) / (ε : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left dist_nonneg (sq_pos_of_pos hεr) hprod
    _ ≤ ((C : ℝ) * dist a b) / (ε : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (hC.dist_le_mul a b) (sq_nonneg _)
    _ = _ := by push_cast; ring

end Reciprocal

section PullbackGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pulledBackGaugeBody (p : F → ℝ) (R : E →ₗᵢ[ℝ] F) : Set E := {x | p (R x) ≤ 1}

noncomputable def pulledBackGaugeRadius (p : F → ℝ) (R : E →ₗᵢ[ℝ] F) : E → ℝ :=
  reciprocalRadial (fun x ↦ p (R x))

theorem IsDefinitePositiveHomogeneous.comp_linearIsometry {p : F → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (R : E →ₗᵢ[ℝ] F) :
    IsDefinitePositiveHomogeneous (fun x ↦ p (R x)) where
  nonneg x := hp.nonneg (R x)
  eq_zero_iff x := by rw [hp.eq_zero_iff, ← R.map_zero, R.injective.eq_iff]
  smul_nonneg t ht x := by rw [R.map_smul]; exact hp.smul_nonneg t ht (R x)

theorem pulledBackGaugeBody_eq_radialBody {p : F → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (R : E →ₗᵢ[ℝ] F) :
    pulledBackGaugeBody p R = radialBody (pulledBackGaugeRadius p R) :=
  (hp.comp_linearIsometry R).sublevel_eq_radialBody

/-- Exact set correspondence with the section of the ambient unit sublevel.
The range premise only identifies which prescribed section is being used. -/
theorem pulledBackGaugeBody_eq_preimage_section (p : F → ℝ) (R : E →ₗᵢ[ℝ] F)
    (H : Submodule ℝ F) (hR : LinearMap.range R.toLinearMap = H) :
    pulledBackGaugeBody p R = R ⁻¹' ({y : F | p y ≤ 1} ∩ (H : Set F)) := by
  ext x
  constructor
  · intro hx
    refine ⟨hx, ?_⟩
    rw [← hR]
    exact LinearMap.mem_range_self R.toLinearMap x
  · intro hx
    exact hx.1

theorem image_pulledBackGaugeBody_eq_section (p : F → ℝ) (R : E →ₗᵢ[ℝ] F)
    (H : Submodule ℝ F) (hR : LinearMap.range R.toLinearMap = H) :
    R '' pulledBackGaugeBody p R = {y : F | p y ≤ 1} ∩ (H : Set F) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨hx, ?_⟩
    rw [← hR]
    exact LinearMap.mem_range_self R.toLinearMap x
  · rintro ⟨hy, hH⟩
    rw [← hR] at hH
    obtain ⟨x, rfl⟩ := hH
    exact ⟨x, hy, rfl⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable {P : Type*} [PseudoMetricSpace P]

/-- All compactness, common-radius, and radial parameter regularity premises
needed for the moment theorem follow from the original ambient gauge and
operator Lipschitz isometric frames. -/
theorem exists_uniform_radial_pulledBackGauge_data {p : F → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (J : P → E →ₗᵢ[ℝ] F) {L : ℝ≥0}
    (hJ : LipschitzWith L (fun a ↦ (J a).toContinuousLinearMap)) :
    ∃ r R : ℝ, ∃ D : ℝ≥0, 0 < r ∧ 0 ≤ R ∧
      (∀ a, IsCompact (radialBody (pulledBackGaugeRadius p (J a)))) ∧
      (∀ a u, ‖u‖ = 1 → r ≤ pulledBackGaugeRadius p (J a) u) ∧
      (∀ a u, ‖u‖ = 1 → pulledBackGaugeRadius p (J a) u ≤ R) ∧
      (∀ u, ‖u‖ = 1 → LipschitzWith D (fun a ↦ pulledBackGaugeRadius p (J a) u)) := by
  obtain ⟨ε, M, hε, hM, hbounds⟩ := hp.exists_sphere_bounds hC.continuousOn
  obtain ⟨Cp, hCp⟩ := hp.exists_lipschitzWith hC
  let εn : ℝ≥0 := ⟨ε, hε.le⟩
  have hεn : 0 < εn := hε
  have hboundsJ : ∀ a u, ‖u‖ = 1 → ε ≤ p (J a u) ∧ p (J a u) ≤ M := by
    intro a u hu
    apply hbounds
    rw [(J a).norm_map, hu]
  refine ⟨M⁻¹, ε⁻¹, (Cp * L) / εn ^ 2, inv_pos.mpr hM, (inv_pos.mpr hε).le, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [← pulledBackGaugeBody_eq_radialBody hp (J a)]
    exact (hp.comp_linearIsometry (J a)).isCompact_sublevel (hCp.comp (J a).lipschitz).lipschitzOnWith
  · intro a u hu
    change M⁻¹ ≤ (p (J a u))⁻¹
    exact (inv_le_inv₀ hM (hε.trans_le (hboundsJ a u hu).1)).mpr (hboundsJ a u hu).2
  · intro a u hu
    change (p (J a u))⁻¹ ≤ ε⁻¹
    exact (inv_le_inv₀ (hε.trans_le (hboundsJ a u hu).1) hε).mpr (hboundsJ a u hu).1
  · intro u hu
    have hJu : LipschitzWith L (fun a ↦ J a u) := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      have heval := ((J a).toContinuousLinearMap - (J b).toContinuousLinearMap).le_opNorm u
      simp only [ContinuousLinearMap.sub_apply, LinearIsometry.coe_toContinuousLinearMap,
        hu, mul_one] at heval
      have hdist : ‖(J a).toContinuousLinearMap - (J b).toContinuousLinearMap‖ ≤ L * dist a b := by
        simpa only [dist_eq_norm] using hJ.dist_le_mul a b
      simpa only [dist_eq_norm] using heval.trans hdist
    exact lipschitzWith_reciprocal_of_positive_lower (hCp.comp hJu) hεn
      (fun a ↦ (hboundsJ a u hu).1)

end PullbackGeometry

section Normalization

variable {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [PseudoMetricSpace P]

/-- All continuous-integrand normalized moments, including the full tensor
moments, depend Lipschitzly on the parameter in the actual pulled-back sections. -/
theorem exists_lipschitzWith_pulledBackGauge_average_family
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {p : F → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (J : P → E →ₗᵢ[ℝ] F) {L : ℝ≥0}
    (hJ : LipschitzWith L (fun a ↦ (J a).toContinuousLinearMap))
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} (hf : Continuous f) :
    ∃ K : ℝ≥0, LipschitzWith K (fun a ↦ ⨍ x in pulledBackGaugeBody p (J a), f x ∂μ) := by
  obtain ⟨r, R, D, hr, hR, hcompact, hlo, hhi, hparam⟩ :=
    exists_uniform_radial_pulledBackGauge_data hp hC J hJ
  obtain ⟨K, hK⟩ := exists_lipschitzWith_radialMoment_family_of_continuous μ
    (fun a ↦ pulledBackGaugeRadius p (J a)) hcompact hr hR hlo hhi hparam hf
  refine ⟨K, ?_⟩
  simpa only [← pulledBackGaugeBody_eq_radialBody hp] using hK

/-- Local covariance normalization of the exact pulled-back sections,
starting from the paper's actual gauge regularity hypothesis. -/
theorem exists_lipschitz_covarianceNormalization_pulledBackSections
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {p : F → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (J : P → E →ₗᵢ[ℝ] F) {L : ℝ≥0}
    (hJ : LipschitzWith L (fun a ↦ (J a).toContinuousLinearMap)) (a₀ : P) :
    ∃ e : P → E ≃L[ℝ] E, ∃ U : Set P, ∃ K : ℝ≥0,
      IsOpen U ∧ a₀ ∈ U ∧ LipschitzOnWith K (fun a ↦ (e a).toContinuousLinearMap) U ∧
      (∀ a ∈ U, covarianceOperator μ ((e a) '' pulledBackGaugeBody p (J a)) =
        ContinuousLinearMap.id ℝ E) := by
  obtain ⟨r, R, D, hr, hR, hcompact, hlo, hhi, hparam⟩ :=
    exists_uniform_radial_pulledBackGauge_data hp hC J hJ
  obtain ⟨e, U, K, hU, ha₀U, heLip, he⟩ :=
    exists_lipschitz_covarianceNormalization_radial_family μ
      (fun a ↦ pulledBackGaugeRadius p (J a)) hcompact hr hR hlo hhi hparam a₀
  refine ⟨e, U, K, hU, ha₀U, heLip, ?_⟩
  intro a ha
  rw [pulledBackGaugeBody_eq_radialBody hp]
  exact he a ha

end Normalization

section ActualSubspaceFamilies

variable {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [PseudoMetricSpace P]

/-- The complete local geometric normalization pipeline on a chart: actual
equal-dimensional subspaces with Lipschitz orthogonal projections give actual
isometric frames on an open parameter domain. Their pulled-back sections are
then put in covariance position by a locally Lipschitz family of genuine
linear equivalences. No moment regularity or frame choice is assumed. -/
theorem exists_local_normalized_section_frames
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {p : F → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (H : P → Submodule ℝ F) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun a ↦ (H a).starProjection))
    (hrank : ∀ a, Module.finrank ℝ (H a) = Module.finrank ℝ E) (a₀ : P) :
    ∃ U : Set P, IsOpen U ∧ a₀ ∈ U ∧
      ∃ J : U → E →ₗᵢ[ℝ] F, ∃ KJ : ℝ≥0,
        LipschitzWith KJ (fun a ↦ (J a).toContinuousLinearMap) ∧
        (∀ a : U, LinearMap.range (J a).toLinearMap = H a.val) ∧
        (∀ a : U, (J a) '' pulledBackGaugeBody p (J a) =
          {y : F | p y ≤ 1} ∩ (H a.val : Set F)) ∧
        (∀ b : U, ∃ e : U → E ≃L[ℝ] E, ∃ W : Set U, ∃ K : ℝ≥0,
          IsOpen W ∧ b ∈ W ∧ LipschitzOnWith K (fun a ↦ (e a).toContinuousLinearMap) W ∧
          (∀ a ∈ W, covarianceOperator μ ((e a) '' pulledBackGaugeBody p (J a)) =
            ContinuousLinearMap.id ℝ E)) := by
  obtain ⟨A, U, KJ, hU, ha₀U, hALip, hA⟩ :=
    exists_lipschitz_isometric_subspace_frames H hLip hrank a₀
  let J : U → E →ₗᵢ[ℝ] F := fun a ↦
    { (A a.val).toLinearMap with
      norm_map' := (A a.val).norm_map_iff_adjoint_comp_self.mpr (hA a.val a.property).1 }
  have hJLip : LipschitzWith KJ (fun a ↦ (J a).toContinuousLinearMap) := hALip.to_restrict
  have hJrange : ∀ a : U, LinearMap.range (J a).toLinearMap = H a.val :=
    fun a ↦ (hA a.val a.property).2
  refine ⟨U, hU, ha₀U, J, KJ, hJLip, hJrange, ?_, ?_⟩
  · intro a
    exact image_pulledBackGaugeBody_eq_section p (J a) (H a.val) (hJrange a)
  · intro b
    exact exists_lipschitz_covarianceNormalization_pulledBackSections μ hp hC J hJLip b

end ActualSubspaceFamilies

end

end BanachIsometric
