import BanachIsometric.StabilizerExponentialChart

/-! Every actual kernel exponential lies in the actual identity component,
by its explicit exponential path. The lift is globally continuous and its
actual local chart is inherited from the proved exponential inverse. Neither
surjectivity onto the identity component nor commutativity is assumed. -/

noncomputable section
namespace BanachIsometric.StabilizerLieCoordinates
open Set
open scoped Topology NNReal

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

def exponentialPath (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) (Y : kernel ρ v) :
    Path (1 : unitaryRepresentationStabilizer ρ v) (exponential ρ v horbit Y) where
  toFun t := exponential ρ v horbit ((t : ℝ) • Y)
  continuous_toFun := (continuous_exponential ρ v horbit).comp
    (continuous_subtype_val.smul continuous_const)
  source' := by simp
  target' := by simp

omit [FiniteDimensional ℝ A] in
theorem exponential_mem_identityComponent (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) (Y : kernel ρ v) :
    exponential ρ v horbit Y ∈
      Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v) := by
  change exponential ρ v horbit Y ∈ connectedComponent (1 : unitaryRepresentationStabilizer ρ v)
  exact pathComponent_subset_component 1 ⟨exponentialPath ρ v horbit Y⟩

def exponentialIdentityComponent (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) (Y : kernel ρ v) :
    Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v) :=
  ⟨exponential ρ v horbit Y, exponential_mem_identityComponent ρ v horbit Y⟩

omit [FiniteDimensional ℝ A] in
@[simp] theorem exponentialIdentityComponent_coe (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) (Y : kernel ρ v) :
    (exponentialIdentityComponent ρ v horbit Y : unitaryRepresentationStabilizer ρ v) =
      exponential ρ v horbit Y := rfl

omit [FiniteDimensional ℝ A] in
@[simp] theorem exponentialIdentityComponent_zero (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    exponentialIdentityComponent ρ v horbit 0 = 1 := by
  apply Subtype.ext
  exact exponential_zero ρ v horbit

omit [FiniteDimensional ℝ A] in
theorem continuous_exponentialIdentityComponent (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    Continuous (exponentialIdentityComponent ρ v horbit) :=
  (continuous_exponential ρ v horbit).subtype_mk _

def identityComponentCoordinates (ρ : A →* Module.End ℝ W) (v : W)
    (R : Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) : kernel ρ v :=
  coordinates ρ v R.val

theorem exists_identityComponent_exponential_openPartialHomeomorph
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∃ e₀ : OpenPartialHomeomorph (kernel ρ v)
        (Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)),
      0 ∈ e₀.source ∧ 1 ∈ e₀.target ∧
      (e₀ : kernel ρ v →
        Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) =
          exponentialIdentityComponent ρ v horbit ∧
      (e₀.symm : Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v) →
        kernel ρ v) = identityComponentCoordinates ρ v := by
  obtain ⟨e, he0, he1, he, hg⟩ := exists_exponential_openPartialHomeomorph ρ v horbit
  let e₀ : OpenPartialHomeomorph (kernel ρ v)
      (Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) := {
    toFun := exponentialIdentityComponent ρ v horbit
    invFun := identityComponentCoordinates ρ v
    source := e.source
    target := Subtype.val ⁻¹' e.target
    map_source' := by
      intro z hz
      change exponential ρ v horbit z ∈ e.target
      rw [← he]
      exact e.map_source hz
    map_target' := by
      intro R hR
      change coordinates ρ v R.val ∈ e.source
      rw [← hg]
      exact e.map_target hR
    left_inv' := by
      intro z hz
      change coordinates ρ v (exponential ρ v horbit z) = z
      rw [← he, ← hg]
      exact e.left_inv hz
    right_inv' := by
      intro R hR
      apply Subtype.ext
      change exponential ρ v horbit (coordinates ρ v R.val) = R.val
      rw [← he, ← hg]
      exact e.right_inv hR
    open_source := e.open_source
    open_target := e.open_target.preimage continuous_subtype_val
    continuousOn_toFun := (continuous_exponentialIdentityComponent ρ v horbit).continuousOn
    continuousOn_invFun := by
      change ContinuousOn (fun R : Subgroup.connectedComponentOfOne
        (unitaryRepresentationStabilizer ρ v) => coordinates ρ v R.val) _
      rw [← hg]
      exact e.symm.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h) }
  exact ⟨e₀, he0, he1, rfl, rfl⟩

end BanachIsometric.StabilizerLieCoordinates
