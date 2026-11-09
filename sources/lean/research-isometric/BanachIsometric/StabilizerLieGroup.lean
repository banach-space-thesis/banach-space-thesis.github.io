import BanachIsometric.StabilizerAnalyticAtlas
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! The stabilizer's actual translated exponential atlas makes multiplication
and inversion analytic. This constructs a Lie group on its existing topology;
no closed-subgroup Lie theorem or homotopy-group finiteness is assumed. -/

noncomputable section
namespace BanachIsometric.StabilizerLieCoordinates
open Set
open scoped Topology NNReal Manifold

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
theorem translatedChart_center
    (ρ : A →* Module.End ℝ W) (v : W)
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (hg : (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v)
    (R : unitaryRepresentationStabilizer ρ v) : translatedChart ρ v e R R = 0 := by
  rw [translatedChart_apply, inv_mul_cancel, hg, coordinates_one]

theorem contDiffAt_mul_in_translated_coordinates
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (he : (e : kernel ρ v → unitaryRepresentationStabilizer ρ v) = exponential ρ v horbit)
    (hg : (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v)
    (R S : unitaryRepresentationStabilizer ρ v) :
    ContDiffAt ℝ ⊤ (fun z : kernel ρ v × kernel ρ v =>
      translatedChart ρ v e (R * S)
        ((translatedChart ρ v e R).symm z.1 * (translatedChart ρ v e S).symm z.2)) 0 := by
  have hExp : ContDiff ℝ ⊤ (fun z : kernel ρ v => ((e z : unitary A) : A)) := by
    rw [he]
    exact (contDiff_algebraExp A).comp (UnitaryOrbit.inclusion A (kernel ρ v)).contDiff
  have he0 : e (0 : kernel ρ v) = 1 := by rw [he, exponential_zero]
  let F : kernel ρ v × kernel ρ v → A := fun z =>
    ((((R * S)⁻¹ : unitaryRepresentationStabilizer ρ v) : unitary A) : A) *
      ((((R : unitary A) : A) * ((e z.1 : unitary A) : A)) *
        (((S : unitary A) : A) * ((e z.2 : unitary A) : A)))
  have hF : ContDiff ℝ ⊤ F := contDiff_const.mul
    ((contDiff_const.mul (hExp.comp contDiff_fst)).mul
      (contDiff_const.mul (hExp.comp contDiff_snd)))
  have hF0 : F 0 = 1 := by
    change ((((R * S)⁻¹ * ((R * e 0) * (S * e 0)) :
      unitaryRepresentationStabilizer ρ v) : unitary A) : A) = 1
    rw [he0, mul_one, mul_one, inv_mul_cancel]
    rfl
  have hC : ContDiffAt ℝ ⊤ (ambientCoordinates ρ v) (F 0) := by
    rw [hF0]
    exact ambientCoordinates_contDiffAt_one ρ v
  have hfun : (fun z : kernel ρ v × kernel ρ v =>
      translatedChart ρ v e (R * S)
        ((translatedChart ρ v e R).symm z.1 * (translatedChart ρ v e S).symm z.2)) =
      ambientCoordinates ρ v ∘ F := by
    funext z
    rw [translatedChart_apply, translatedChart_symm_apply, translatedChart_symm_apply, hg]
    rfl
  rw [hfun]
  exact hC.comp 0 hF.contDiffAt

theorem contDiffAt_inv_in_translated_coordinates
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (he : (e : kernel ρ v → unitaryRepresentationStabilizer ρ v) = exponential ρ v horbit)
    (hg : (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v)
    (R : unitaryRepresentationStabilizer ρ v) :
    ContDiffAt ℝ ⊤ (fun z : kernel ρ v => translatedChart ρ v e R⁻¹
      ((translatedChart ρ v e R).symm z)⁻¹) 0 := by
  have hExp : ContDiff ℝ ⊤ (fun z : kernel ρ v => ((e z : unitary A) : A)) := by
    rw [he]
    exact (contDiff_algebraExp A).comp (UnitaryOrbit.inclusion A (kernel ρ v)).contDiff
  have he0 : e (0 : kernel ρ v) = 1 := by rw [he, exponential_zero]
  let F : kernel ρ v → A := fun z =>
    ((R : unitary A) : A) * star (((R : unitary A) : A) * ((e z : unitary A) : A))
  have hF : ContDiff ℝ ⊤ F := contDiff_const.mul
    ((starL' ℝ : A ≃L[ℝ] A).contDiff.comp (contDiff_const.mul hExp))
  have hF0 : F 0 = 1 := by
    change (((R * (R * e 0)⁻¹ : unitaryRepresentationStabilizer ρ v) : unitary A) : A) = 1
    rw [he0, mul_one, mul_inv_cancel]
    rfl
  have hC : ContDiffAt ℝ ⊤ (ambientCoordinates ρ v) (F 0) := by
    rw [hF0]
    exact ambientCoordinates_contDiffAt_one ρ v
  have hfun : (fun z : kernel ρ v => translatedChart ρ v e R⁻¹
      ((translatedChart ρ v e R).symm z)⁻¹) = ambientCoordinates ρ v ∘ F := by
    funext z
    rw [translatedChart_apply, translatedChart_symm_apply, inv_inv, hg]
    rfl
  rw [hfun]
  exact hC.comp 0 hF.contDiffAt

theorem contMDiff_mul_translatedChartedSpace
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (he1 : 1 ∈ e.target)
    (he : (e : kernel ρ v → unitaryRepresentationStabilizer ρ v) = exponential ρ v horbit)
    (hg : (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v) :
    letI := translatedChartedSpace ρ v e he1
    ContMDiff ((modelWithCornersSelf ℝ (kernel ρ v)).prod (modelWithCornersSelf ℝ (kernel ρ v)))
      (modelWithCornersSelf ℝ (kernel ρ v)) ⊤
      (fun p : unitaryRepresentationStabilizer ρ v × unitaryRepresentationStabilizer ρ v => p.1 * p.2) := by
  letI := translatedChartedSpace ρ v e he1
  rintro ⟨R, S⟩
  rw [contMDiffAt_iff]
  refine ⟨continuous_mul.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ⊤ (fun z : kernel ρ v × kernel ρ v =>
    translatedChart ρ v e (R * S)
      ((translatedChart ρ v e R).symm z.1 * (translatedChart ρ v e S).symm z.2)) _
      (translatedChart ρ v e R R, translatedChart ρ v e S S)
  rw [translatedChart_center ρ v e hg R, translatedChart_center ρ v e hg S]
  exact (contDiffAt_mul_in_translated_coordinates ρ v horbit e he hg R S).contDiffWithinAt

theorem contMDiff_inv_translatedChartedSpace
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (he1 : 1 ∈ e.target)
    (he : (e : kernel ρ v → unitaryRepresentationStabilizer ρ v) = exponential ρ v horbit)
    (hg : (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v) :
    letI := translatedChartedSpace ρ v e he1
    ContMDiff (modelWithCornersSelf ℝ (kernel ρ v)) (modelWithCornersSelf ℝ (kernel ρ v)) ⊤
      (fun R : unitaryRepresentationStabilizer ρ v => R⁻¹) := by
  letI := translatedChartedSpace ρ v e he1
  intro R
  rw [contMDiffAt_iff]
  refine ⟨continuous_inv.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ⊤ (fun z : kernel ρ v => translatedChart ρ v e R⁻¹
    ((translatedChart ρ v e R).symm z)⁻¹) _ (translatedChart ρ v e R R)
  rw [translatedChart_center ρ v e hg R]
  exact (contDiffAt_inv_in_translated_coordinates ρ v horbit e he hg R).contDiffWithinAt

theorem lieGroup_translatedChartedSpace
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (he1 : 1 ∈ e.target)
    (he : (e : kernel ρ v → unitaryRepresentationStabilizer ρ v) = exponential ρ v horbit)
    (hg : (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v)
    (hcoords : ∀ R ∈ e.target,
      ContDiffAt ℝ ⊤ (ambientCoordinates ρ v) ((R : unitary A) : A)) :
    letI := translatedChartedSpace ρ v e he1
    LieGroup (modelWithCornersSelf ℝ (kernel ρ v)) ⊤ (unitaryRepresentationStabilizer ρ v) := by
  letI := translatedChartedSpace ρ v e he1
  exact {
    toContMDiffMul := {
      toIsManifold := isManifold_translatedChartedSpace ρ v horbit e he1 he hg hcoords
      contMDiff_mul := contMDiff_mul_translatedChartedSpace ρ v horbit e he1 he hg }
    contMDiff_inv := contMDiff_inv_translatedChartedSpace ρ v horbit e he1 he hg }

theorem exists_analytic_lieGroup
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∃ c : ChartedSpace (kernel ρ v) (unitaryRepresentationStabilizer ρ v),
      letI := c
      LieGroup (modelWithCornersSelf ℝ (kernel ρ v)) ⊤
        (unitaryRepresentationStabilizer ρ v) := by
  obtain ⟨e, _he0, he1, he, hg, hcoords⟩ :=
    exists_analytic_exponential_openPartialHomeomorph ρ v horbit
  exact ⟨translatedChartedSpace ρ v e he1,
    lieGroup_translatedChartedSpace ρ v horbit e he1 he hg hcoords⟩

theorem exists_compact_analytic_lieGroup [CompactSpace (unitary A)]
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∃ c : ChartedSpace (kernel ρ v) (unitaryRepresentationStabilizer ρ v),
      letI := c
      LieGroup (modelWithCornersSelf ℝ (kernel ρ v)) ⊤
        (unitaryRepresentationStabilizer ρ v) ∧
      CompactSpace (unitaryRepresentationStabilizer ρ v) := by
  obtain ⟨c, hc⟩ := exists_analytic_lieGroup ρ v horbit
  refine ⟨c, hc, ?_⟩
  exact isCompact_iff_compactSpace.mp
    (isClosed_unitaryRepresentationStabilizer ρ v horbit.continuous).isCompact

end BanachIsometric.StabilizerLieCoordinates
