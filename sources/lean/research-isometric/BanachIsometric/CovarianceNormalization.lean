import BanachIsometric.Covariance
import BanachIsometric.MomentRegularity
import BanachIsometric.LocalCovarianceFactor

/-!
# Locally Lipschitz covariance normalization of actual bodies

This combines the moment-integral estimates with the local algebraic factor.
The operators here act on the original real inner-product space. In particular
no inner-product structure is silently installed on a sup-norm coordinate space.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal

noncomputable section

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]

theorem covarianceOperator_isSelfAdjoint (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {S : Set G} (hS : IsCompact S) : IsSelfAdjoint (covarianceOperator μ S) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (covarianceOperator_inner_symm μ hS)

variable {P : Type*} [PseudoMetricSpace P]

/-- A locally Lipschitz family of actual linear equivalences putting a family
of compact bodies into covariance position near a reference body already in
that position. The Lipschitz norm is the original operator norm. -/
theorem exists_lipschitz_covariancePosition_family (μ : Measure G)
    [Measure.IsAddHaarMeasure μ] (S : P → Set G) (hcompact : ∀ a, IsCompact (S a))
    (a₀ : P) (hbase : covarianceOperator μ (S a₀) = ContinuousLinearMap.id ℝ G)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun a ↦ covarianceOperator μ (S a))) :
    ∃ e : P → G ≃L[ℝ] G, ∃ U : Set P, ∃ K : ℝ≥0,
      IsOpen U ∧ a₀ ∈ U ∧ e a₀ = ContinuousLinearEquiv.refl ℝ G ∧
      LipschitzOnWith K (fun a ↦ (e a).toContinuousLinearMap) U ∧
      (∀ a ∈ U, covarianceOperator μ ((e a) '' S a) = ContinuousLinearMap.id ℝ G) := by
  classical
  let C : P → (G →L[ℝ] G) := fun a ↦ covarianceOperator μ (S a)
  have hC0 : C a₀ = 1 := hbase
  obtain ⟨Q, V, KQ, hV, h1V, hQ1, hQLip, hQunit, hQwhite⟩ :=
    exists_lipschitz_local_covarianceWhitening (A := G →L[ℝ] G)
  let U : Set P := C ⁻¹' V
  have hUopen : IsOpen U := hV.preimage hLip.continuous
  have ha₀U : a₀ ∈ U := by change C a₀ ∈ V; rwa [hC0]
  let e : P → G ≃L[ℝ] G := fun a ↦
    if hu : IsUnit (Q (C a)) then ContinuousLinearEquiv.ofUnit hu.unit
    else ContinuousLinearEquiv.refl ℝ G
  have he : ∀ a ∈ U, (e a).toContinuousLinearMap = Q (C a) := by
    intro a ha
    have hu := hQunit (C a) ha
    simp only [e, dif_pos hu]
    ext x
    exact congrArg (fun f : G →L[ℝ] G ↦ f x) hu.unit_spec
  refine ⟨e, U, KQ * L, hUopen, ha₀U, ?_, ?_, ?_⟩
  · ext x
    change (e a₀).toContinuousLinearMap x = x
    rw [he a₀ ha₀U, hC0, hQ1]
    rfl
  · have h := hQLip.comp hLip.lipschitzOnWith (mapsTo_preimage C V)
    intro a ha b hb
    simpa only [he a ha, he b hb] using h ha hb
  · intro a ha
    have hself := covarianceOperator_isSelfAdjoint μ (hcompact a)
    have hwhite := (hQwhite (C a) ha hself).2
    rw [covarianceOperator_image μ (hcompact a) (e a), he a ha]
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.one_def, ContinuousLinearMap.comp_assoc, C] using hwhite

/-- Direct radial-family form: the hypothesis concerns the radial functions
themselves, and both moment Lipschitz regularity and the normalization are
proved. This is the normalization part of Proposition 4.2 by homothetic shells
and the square-map inverse function theorem. -/
theorem exists_lipschitz_covariancePosition_radial_family (μ : Measure G)
    [Measure.IsAddHaarMeasure μ] (ρ : P → G → ℝ)
    (hcompact : ∀ a, IsCompact (radialBody (ρ a)))
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlo : ∀ a u, ‖u‖ = 1 → r ≤ ρ a u)
    (hhi : ∀ a u, ‖u‖ = 1 → ρ a u ≤ R)
    {L : ℝ≥0} (hparam : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a ↦ ρ a u))
    (a₀ : P)
    (hbase : covarianceOperator μ (radialBody (ρ a₀)) = ContinuousLinearMap.id ℝ G) :
    ∃ e : P → G ≃L[ℝ] G, ∃ U : Set P, ∃ K : ℝ≥0,
      IsOpen U ∧ a₀ ∈ U ∧ e a₀ = ContinuousLinearEquiv.refl ℝ G ∧
      LipschitzOnWith K (fun a ↦ (e a).toContinuousLinearMap) U ∧
      (∀ a ∈ U, covarianceOperator μ ((e a) '' radialBody (ρ a)) =
        ContinuousLinearMap.id ℝ G) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_radialMoment_family_of_continuous
    μ ρ hcompact hr hR hlo hhi hparam continuous_rankOneCovariance
  have hCov : LipschitzWith K (fun a ↦ covarianceOperator μ (radialBody (ρ a))) := by
    simpa only [setAverage_eq, covarianceOperator] using hK
  exact exists_lipschitz_covariancePosition_family μ (fun a ↦ radialBody (ρ a))
    hcompact a₀ hbase hCov

/-- The reference covariance need not be the identity: a fixed genuine
normalization is first constructed, and the Lipschitz correction is then
composed with it. Only the reference body must contain a neighbourhood of zero. -/
theorem exists_lipschitz_covarianceNormalization_family (μ : Measure G)
    [Measure.IsAddHaarMeasure μ] (S : P → Set G) (hcompact : ∀ a, IsCompact (S a))
    (a₀ : P) (h0 : (0 : G) ∈ interior (S a₀))
    {L : ℝ≥0} (hLip : LipschitzWith L (fun a ↦ covarianceOperator μ (S a))) :
    ∃ e : P → G ≃L[ℝ] G, ∃ U : Set P, ∃ K : ℝ≥0,
      IsOpen U ∧ a₀ ∈ U ∧
      LipschitzOnWith K (fun a ↦ (e a).toContinuousLinearMap) U ∧
      (∀ a ∈ U, covarianceOperator μ ((e a) '' S a) = ContinuousLinearMap.id ℝ G) := by
  obtain ⟨e₀, he₀⟩ := exists_covariancePosition μ (hcompact a₀) h0
  let T : P → Set G := fun a ↦ e₀ '' S a
  have hTcompact : ∀ a, IsCompact (T a) := fun a ↦ (hcompact a).image e₀.continuous
  let D := ContinuousLinearMap.mulLeftRight ℝ (G →L[ℝ] G)
    e₀.toContinuousLinearMap e₀.toContinuousLinearMap.adjoint
  have hD : ∀ a, D (covarianceOperator μ (S a)) = covarianceOperator μ (T a) := by
    intro a
    rw [covarianceOperator_image μ (hcompact a) e₀]
    simp only [D, ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc]
  have hTLip : LipschitzWith (‖D‖₊ * L) (fun a ↦ covarianceOperator μ (T a)) := by
    simpa only [Function.comp_def, hD] using D.lipschitz.comp hLip
  obtain ⟨d, U, K, hU, ha₀U, hd0, hdLip, hdNorm⟩ :=
    exists_lipschitz_covariancePosition_family μ T hTcompact a₀ he₀ hTLip
  let e : P → G ≃L[ℝ] G := fun a ↦ e₀.trans (d a)
  let M := (ContinuousLinearMap.mul ℝ (G →L[ℝ] G)).flip e₀.toContinuousLinearMap
  refine ⟨e, U, ‖M‖₊ * K, hU, ha₀U, ?_, ?_⟩
  · have hM := M.lipschitz.lipschitzOnWith.comp hdLip (fun _ _ ↦ mem_univ _)
    intro a ha b hb
    change edist ((d a).toContinuousLinearMap * e₀.toContinuousLinearMap)
      ((d b).toContinuousLinearMap * e₀.toContinuousLinearMap) ≤ _
    exact hM ha hb
  · intro a ha
    have himage : (e a) '' S a = (d a) '' T a := by rw [image_image]; rfl
    rw [himage]
    exact hdNorm a ha

/-- Complete normalization statement for radial families, with neither a
normalization assumption at the reference point nor an assumed covariance
regularity theorem. The common inner radius supplies the interior condition. -/
theorem exists_lipschitz_covarianceNormalization_radial_family (μ : Measure G)
    [Measure.IsAddHaarMeasure μ] (ρ : P → G → ℝ)
    (hcompact : ∀ a, IsCompact (radialBody (ρ a)))
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlo : ∀ a u, ‖u‖ = 1 → r ≤ ρ a u)
    (hhi : ∀ a u, ‖u‖ = 1 → ρ a u ≤ R)
    {L : ℝ≥0} (hparam : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a ↦ ρ a u))
    (a₀ : P) :
    ∃ e : P → G ≃L[ℝ] G, ∃ U : Set P, ∃ K : ℝ≥0,
      IsOpen U ∧ a₀ ∈ U ∧
      LipschitzOnWith K (fun a ↦ (e a).toContinuousLinearMap) U ∧
      (∀ a ∈ U, covarianceOperator μ ((e a) '' radialBody (ρ a)) =
        ContinuousLinearMap.id ℝ G) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_radialMoment_family_of_continuous
    μ ρ hcompact hr hR hlo hhi hparam continuous_rankOneCovariance
  have hCov : LipschitzWith K (fun a ↦ covarianceOperator μ (radialBody (ρ a))) := by
    simpa only [setAverage_eq, covarianceOperator] using hK
  have h0 : (0 : G) ∈ interior (radialBody (ρ a₀)) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      (Metric.closedBall_mem_nhds (0 : G) hr) (closedBall_subset_radialBody (hlo a₀)))
  exact exists_lipschitz_covarianceNormalization_family μ (fun a ↦ radialBody (ρ a))
    hcompact a₀ h0 hCov

end

end BanachIsometric
