import BanachIsometric.StabilizerExponentialChart
import BanachIsometric.ExponentialCoordinatesSmooth

/-! The actual exponential chart can be restricted to an ambient analytic
coordinate neighborhood. The coordinate function is the previously constructed
IFT function, not an abstract chart given with a smoothness premise. -/

noncomputable section
namespace BanachIsometric.StabilizerLieCoordinates
open Set Filter
open scoped Topology NNReal

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

def ambientCoordinates (ρ : A →* Module.End ℝ W) (v : W) (R : A) : kernel ρ v :=
  (SkewFactorization.coordinates A (complement ρ v) (kernel ρ v)
    (complement_isCompl ρ v) R).2

omit [FiniteDimensional ℝ W] in
@[simp] theorem ambientCoordinates_coe (ρ : A →* Module.End ℝ W) (v : W)
    (R : unitaryRepresentationStabilizer ρ v) :
    ambientCoordinates ρ v ((R : unitary A) : A) = coordinates ρ v R := rfl

omit [FiniteDimensional ℝ W] in
theorem ambientCoordinates_contDiffAt_one (ρ : A →* Module.End ℝ W) (v : W) :
    ContDiffAt ℝ ⊤ (ambientCoordinates ρ v) 1 :=
  contDiff_snd.contDiffAt.comp 1
    (SkewFactorization.coordinates_contDiffAt_one A (complement ρ v) (kernel ρ v)
      (complement_isCompl ρ v))

theorem exists_analytic_exponential_openPartialHomeomorph
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∃ e : OpenPartialHomeomorph (kernel ρ v) (unitaryRepresentationStabilizer ρ v),
      0 ∈ e.source ∧ 1 ∈ e.target ∧
      (e : kernel ρ v → unitaryRepresentationStabilizer ρ v) = exponential ρ v horbit ∧
      (e.symm : unitaryRepresentationStabilizer ρ v → kernel ρ v) = coordinates ρ v ∧
      ∀ R ∈ e.target, ContDiffAt ℝ ⊤ (ambientCoordinates ρ v) ((R : unitary A) : A) := by
  obtain ⟨e, _he0, he1, hf, hg⟩ := exists_exponential_openPartialHomeomorph ρ v horbit
  have hevent : ∀ᶠ R : A in 𝓝 1, ContDiffAt ℝ ⊤ (ambientCoordinates ρ v) R :=
    (ambientCoordinates_contDiffAt_one ρ v).eventually (by simp)
  obtain ⟨N, hNsub, hNopen, h1N⟩ := mem_nhds_iff.mp hevent
  let val : unitaryRepresentationStabilizer ρ v → A := fun R => ((R : unitary A) : A)
  have hval : Continuous val := continuous_subtype_val.comp continuous_subtype_val
  let B := val ⁻¹' N
  have hB : IsOpen B := hNopen.preimage hval
  let χ := e.symm.restrOpen B hB
  have h1χ : (1 : unitaryRepresentationStabilizer ρ v) ∈ χ.source := by
    refine ⟨he1, ?_⟩
    exact h1N
  have hχ1 : χ (1 : unitaryRepresentationStabilizer ρ v) = 0 := by
    change e.symm 1 = 0
    rw [hg, coordinates_one]
  have h0χ : (0 : kernel ρ v) ∈ χ.target := hχ1 ▸ χ.map_source h1χ
  refine ⟨χ.symm, h0χ, h1χ, hf, hg, ?_⟩
  intro R hR
  exact hNsub hR.2

end BanachIsometric.StabilizerLieCoordinates
