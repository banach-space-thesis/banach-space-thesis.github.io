import BanachIsometric.StabilizerAnalyticChart
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! Actual translated exponential charts have analytic changes of coordinates.
The coordinate extension is the proved analytic IFT inverse and all chart
domains are actual open subsets of the stabilizer's existing topology. -/

noncomputable section
namespace BanachIsometric.StabilizerLieCoordinates
open Set
open scoped Topology NNReal Manifold

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [CompleteSpace A] [FiniteDimensional ℝ A] [FiniteDimensional ℝ W] in
theorem translatedChart_apply (ρ : A →* Module.End ℝ W) (v : W)
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (R S : unitaryRepresentationStabilizer ρ v) :
    translatedChart ρ v e R S = e.symm (R⁻¹ * S) := rfl

omit [CompleteSpace A] [FiniteDimensional ℝ A] [FiniteDimensional ℝ W] in
theorem translatedChart_symm_apply (ρ : A →* Module.End ℝ W) (v : W)
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (R : unitaryRepresentationStabilizer ρ v) (z : kernel ρ v) :
    (translatedChart ρ v e R).symm z = R * e z := by
  change (Homeomorph.mulLeft R⁻¹).symm (e z) = _
  rw [Homeomorph.mulLeft_symm, inv_inv]
  rfl

omit [CompleteSpace A] [FiniteDimensional ℝ A] [FiniteDimensional ℝ W] in
theorem mem_translatedChart_source (ρ : A →* Module.End ℝ W) (v : W)
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (R S : unitaryRepresentationStabilizer ρ v) :
    S ∈ (translatedChart ρ v e R).source ↔ R⁻¹ * S ∈ e.target := by
  change (S ∈ univ ∧ R⁻¹ * S ∈ e.target) ↔ _
  exact and_iff_right (mem_univ S)

theorem translated_transition_contDiffOn
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (he : (e : kernel ρ v → unitaryRepresentationStabilizer ρ v) = exponential ρ v horbit)
    (hg : (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v)
    (hcoords : ∀ R ∈ e.target,
      ContDiffAt ℝ ⊤ (ambientCoordinates ρ v) ((R : unitary A) : A))
    (R S : unitaryRepresentationStabilizer ρ v) :
    ContDiffOn ℝ ⊤ ((translatedChart ρ v e R).symm.trans (translatedChart ρ v e S))
      ((translatedChart ρ v e R).symm.trans (translatedChart ρ v e S)).source := by
  have hExp : ContDiff ℝ ⊤ (fun z : kernel ρ v => ((e z : unitary A) : A)) := by
    rw [he]
    exact (contDiff_algebraExp A).comp (UnitaryOrbit.inclusion A (kernel ρ v)).contDiff
  let F : kernel ρ v → A := fun z =>
    (((S⁻¹ : unitaryRepresentationStabilizer ρ v) : unitary A) : A) *
      (((R : unitary A) : A) * ((e z : unitary A) : A))
  have hF : ContDiff ℝ ⊤ F := contDiff_const.mul (contDiff_const.mul hExp)
  have hfun : (((translatedChart ρ v e R).symm.trans (translatedChart ρ v e S)) :
      kernel ρ v → kernel ρ v) = ambientCoordinates ρ v ∘ F := by
    funext z
    rw [OpenPartialHomeomorph.trans_apply, translatedChart_apply, translatedChart_symm_apply, hg]
    rfl
  intro z hz
  have htarget : S⁻¹ * (R * e z) ∈ e.target := by
    have h := (mem_translatedChart_source ρ v e S
      ((translatedChart ρ v e R).symm z)).mp hz.2
    rwa [translatedChart_symm_apply] at h
  have h := (hcoords (S⁻¹ * (R * e z)) htarget).comp z hF.contDiffAt
  rw [hfun]
  exact h.contDiffWithinAt

theorem isManifold_translatedChartedSpace
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (he1 : 1 ∈ e.target)
    (he : (e : kernel ρ v → unitaryRepresentationStabilizer ρ v) = exponential ρ v horbit)
    (hg : (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v)
    (hcoords : ∀ R ∈ e.target,
      ContDiffAt ℝ ⊤ (ambientCoordinates ρ v) ((R : unitary A) : A)) :
    letI := translatedChartedSpace ρ v e he1
    IsManifold (modelWithCornersSelf ℝ (kernel ρ v)) ⊤ (unitaryRepresentationStabilizer ρ v) := by
  letI := translatedChartedSpace ρ v e he1
  apply isManifold_of_contDiffOn (modelWithCornersSelf ℝ (kernel ρ v)) ⊤
  intro c d hc hd
  change c ∈ range (translatedChart ρ v e) at hc
  change d ∈ range (translatedChart ρ v e) at hd
  obtain ⟨R, rfl⟩ := hc
  obtain ⟨S, rfl⟩ := hd
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ] using
    translated_transition_contDiffOn ρ v horbit e he hg hcoords R S

/-- An actual analytic manifold structure on the original stabilizer topology.
All local charts and their analytic coordinate neighborhoods are constructed. -/
theorem exists_analytic_chartedSpace
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∃ c : ChartedSpace (kernel ρ v) (unitaryRepresentationStabilizer ρ v),
      letI := c
      IsManifold (modelWithCornersSelf ℝ (kernel ρ v)) ⊤
        (unitaryRepresentationStabilizer ρ v) := by
  obtain ⟨e, _he0, he1, he, hg, hcoords⟩ :=
    exists_analytic_exponential_openPartialHomeomorph ρ v horbit
  exact ⟨translatedChartedSpace ρ v e he1,
    isManifold_translatedChartedSpace ρ v horbit e he1 he hg hcoords⟩

end BanachIsometric.StabilizerLieCoordinates
