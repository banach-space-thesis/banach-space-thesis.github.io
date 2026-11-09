import BanachIsometric.StabilizerLieInverse
import BanachIsometric.LocalInverseHomeomorph
import Mathlib.Geometry.Manifold.ChartedSpace

/-! The actual stabilizer is locally Euclidean, with an explicit exponential
open partial homeomorphism from the actual orbit-derivative kernel. Translating
that chart gives an actual charted-space structure. This is a topological
chart theorem, not a proof of smooth Lie compatibility or higher homotopy
torsion. -/

noncomputable section
namespace BanachIsometric.StabilizerLieCoordinates
open Set
open scoped Topology NNReal

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem exists_exponential_openPartialHomeomorph (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∃ e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v),
      0 ∈ e.source ∧ 1 ∈ e.target ∧
      (e : kernel ρ v → unitaryRepresentationStabilizer ρ v) = exponential ρ v horbit ∧
      (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v := by
  obtain ⟨N, hN, L, hLip⟩ := coordinates_lipschitzOn_nhds ρ v
  exact exists_openPartialHomeomorph_of_eventual_inverses
    (exponential ρ v horbit) (coordinates ρ v) 0 1
    (exponential_zero ρ v horbit) (coordinates_one ρ v) (continuous_exponential ρ v horbit)
    hN hLip.continuousOn (coordinates_exponential ρ v horbit) (exponential_coordinates ρ v horbit)

def translatedChart (ρ : A →* Module.End ℝ W) (v : W)
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (R : unitaryRepresentationStabilizer ρ v) :
    OpenPartialHomeomorph (unitaryRepresentationStabilizer ρ v) (kernel ρ v) :=
  (Homeomorph.mulLeft R⁻¹).toOpenPartialHomeomorph.trans e.symm

def translatedChartedSpace (ρ : A →* Module.End ℝ W) (v : W)
    (e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v))
    (he1 : 1 ∈ e.target) :
    ChartedSpace (kernel ρ v) (unitaryRepresentationStabilizer ρ v) := by
  refine {
    atlas := Set.range (translatedChart ρ v e)
    chartAt := translatedChart ρ v e
    mem_chart_source := ?_
    chart_mem_atlas := fun R => ⟨R, rfl⟩ }
  intro R
  change R ∈ Set.univ ∧ (Homeomorph.mulLeft R⁻¹) R ∈ e.target
  refine ⟨mem_univ _, ?_⟩
  simpa only [Homeomorph.coe_mulLeft, inv_mul_cancel] using he1

theorem nonempty_chartedSpace (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    Nonempty (ChartedSpace (kernel ρ v) (unitaryRepresentationStabilizer ρ v)) := by
  obtain ⟨e, _he0, he1, _hf, _hg⟩ := exists_exponential_openPartialHomeomorph ρ v horbit
  exact ⟨translatedChartedSpace ρ v e he1⟩

end BanachIsometric.StabilizerLieCoordinates
