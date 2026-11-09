import BanachIsometric.StabilizerComponents

/-! Actual local exponential coordinates for the representation stabilizer.
The coordinate space is the kernel of the actual orbit derivative, and both
local inverse identities are proved from the existing exponential IFT slice.
No closed-subgroup Lie theorem or higher-homotopy finiteness is a premise. -/

noncomputable section
namespace BanachIsometric.StabilizerLieCoordinates
open Set Filter
open scoped Topology NNReal

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

def expOrbit (ρ : A →* Module.End ℝ W) (v : W) (X : A) : W := ρ (NormedSpace.exp ℝ X) v

def derivative (ρ : A →* Module.End ℝ W) (v : W) : UnitaryOrbit.Skew A →L[ℝ] W :=
  (fderiv ℝ (expOrbit ρ v) 0).comp (skewAdjoint.submodule ℝ A).subtypeL

def kernel (ρ : A →* Module.End ℝ W) (v : W) : Submodule ℝ (UnitaryOrbit.Skew A) :=
  LinearMap.ker (derivative ρ v).toLinearMap

def complement (ρ : A →* Module.End ℝ W) (v : W) : Submodule ℝ (UnitaryOrbit.Skew A) :=
  ((kernel ρ v).exists_isCompl).choose

omit [CompleteSpace A] [ContinuousStar A] [FiniteDimensional ℝ A] [FiniteDimensional ℝ W] in
theorem complement_isCompl (ρ : A →* Module.End ℝ W) (v : W) :
    IsCompl (complement ρ v) (kernel ρ v) := ((kernel ρ v).exists_isCompl).choose_spec.symm

omit [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A] [FiniteDimensional ℝ W] in
theorem expOrbit_hasStrictFDerivAt_zero (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    HasStrictFDerivAt (expOrbit ρ v) (fderiv ℝ (expOrbit ρ v) 0) 0 := by
  have hO : HasStrictFDerivAt (fun R : A => ρ R v)
      (fderiv ℝ (fun R : A => ρ R v) 1) (NormedSpace.exp ℝ (0 : A)) := by
    simpa only [NormedSpace.exp_zero] using horbit.hasStrictFDerivAt (x := (1 : A)) (by simp)
  have h := hO.comp (0 : A) (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
  change HasStrictFDerivAt (expOrbit ρ v) _ 0 at h
  rw [h.hasFDerivAt.fderiv]
  exact h

def exponential (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) (Y : kernel ρ v) :
    unitaryRepresentationStabilizer ρ v := by
  refine ⟨UnitaryOrbit.exponential A (kernel ρ v) Y, ?_⟩
  have hY : fderiv ℝ (expOrbit ρ v) 0 (((Y : UnitaryOrbit.Skew A) : A)) = 0 := Y.property
  have h := representation_exp_fixed_of_fderiv_eq_zero ρ v
    (expOrbit_hasStrictFDerivAt_zero ρ v horbit).differentiableAt _ hY (1 : ℝ)
  simpa only [one_smul] using h

def coordinates (ρ : A →* Module.End ℝ W) (v : W)
    (R : unitaryRepresentationStabilizer ρ v) : kernel ρ v :=
  (SkewFactorization.coordinates A (complement ρ v) (kernel ρ v)
    (complement_isCompl ρ v) ((R : unitary A) : A)).2

omit [FiniteDimensional ℝ A] in
@[simp] theorem exponential_zero (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) : exponential ρ v horbit 0 = 1 := by
  apply Subtype.ext
  exact UnitaryOrbit.exponential_zero A (kernel ρ v)

omit [FiniteDimensional ℝ W] in
@[simp] theorem coordinates_one (ρ : A →* Module.End ℝ W) (v : W) : coordinates ρ v 1 = 0 := by
  simp [coordinates]

omit [FiniteDimensional ℝ A] in
theorem continuous_exponential (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) : Continuous (exponential ρ v horbit) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (NormedSpace.exp_continuous (𝕂 := ℝ)).comp (UnitaryOrbit.inclusion A (kernel ρ v)).continuous

omit [FiniteDimensional ℝ W] in
theorem coordinates_continuousAt_one (ρ : A →* Module.End ℝ W) (v : W) :
    ContinuousAt (coordinates ρ v) 1 := by
  have hval : ContinuousAt (fun R : unitaryRepresentationStabilizer ρ v => ((R : unitary A) : A)) 1 :=
    continuous_subtype_val.continuousAt.comp continuous_subtype_val.continuousAt
  have hzA : ContinuousAt (SkewFactorization.coordinates A (complement ρ v) (kernel ρ v)
      (complement_isCompl ρ v)) (1 : A) :=
    (SkewFactorization.coordinates_hasStrictFDerivAt A (complement ρ v) (kernel ρ v)
      (complement_isCompl ρ v)).continuousAt
  have hz := hzA.comp
    (f := fun R : unitaryRepresentationStabilizer ρ v => ((R : unitary A) : A)) hval
  exact continuous_snd.continuousAt.comp hz

omit [FiniteDimensional ℝ W] in
theorem coordinates_lipschitzOn_nhds (ρ : A →* Module.End ℝ W) (v : W) :
    ∃ U ∈ 𝓝 (1 : unitaryRepresentationStabilizer ρ v), ∃ L : ℝ≥0,
      LipschitzOnWith L (coordinates ρ v) U := by
  obtain ⟨N, hN, L, hLip⟩ := SkewFactorization.coordinates_lipschitzOn_nhds
    A (complement ρ v) (kernel ρ v) (complement_isCompl ρ v)
  let val : unitaryRepresentationStabilizer ρ v → A := fun R => ((R : unitary A) : A)
  have hval : LipschitzWith (1 * 1) val :=
    (LipschitzWith.subtype_val _).comp (LipschitzWith.subtype_val _)
  let U := val ⁻¹' N
  have hU : U ∈ 𝓝 (1 : unitaryRepresentationStabilizer ρ v) :=
    hval.continuous.continuousAt.preimage_mem_nhds hN
  have hcomp := hLip.comp hval.lipschitzOnWith (fun _ h => h)
  exact ⟨U, hU, 1 * (L * (1 * 1)), (LipschitzWith.prod_snd).comp_lipschitzOnWith hcomp⟩

omit [CompleteSpace A] [ContinuousStar A] [FiniteDimensional ℝ A] [FiniteDimensional ℝ W] in
theorem expProduct_zero_fst (ρ : A →* Module.End ℝ W) (v : W) (Y : kernel ρ v) :
    SkewFactorization.expProduct A (complement ρ v) (kernel ρ v) (0, Y) =
      NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (kernel ρ v) Y) := by
  change NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (complement ρ v) 0) *
    NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (kernel ρ v) Y) = _
  rw [map_zero, NormedSpace.exp_zero, one_mul]

theorem coordinates_exponential (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∀ᶠ Y : kernel ρ v in 𝓝 0, coordinates ρ v (exponential ρ v horbit Y) = Y := by
  let U := complement ρ v
  let K := kernel ρ v
  let hc := complement_isCompl ρ v
  have hleft : ∀ᶠ z : U × K in 𝓝 0,
      SkewFactorization.localInverse A U K hc (SkewFactorization.factorMap A U K z) = z := by
    simpa only [SkewFactorization.localInverse] using
      (SkewFactorization.factorMap_hasStrictFDerivAt A U K hc).eventually_left_inverse
  have hto : Tendsto (fun Y : K => ((0 : U), Y)) (𝓝 0) (𝓝 0) :=
    (continuous_const.prodMk continuous_id).tendsto 0
  filter_upwards [hto.eventually hleft] with Y hY
  change SkewFactorization.coordinates A U K hc (SkewFactorization.expProduct A U K (0, Y)) =
    (0, Y) at hY
  have hs := congrArg Prod.snd hY
  change (SkewFactorization.coordinates A U K hc
    (NormedSpace.exp ℝ (UnitaryOrbit.inclusion A K Y))).2 = Y
  rw [← expProduct_zero_fst ρ v Y]
  exact hs

end BanachIsometric.StabilizerLieCoordinates
