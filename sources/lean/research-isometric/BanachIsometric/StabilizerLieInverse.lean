import BanachIsometric.StabilizerLieCoordinates

/-! The remaining inverse identity for actual stabilizer exponential
coordinates. The complementary orbit coordinate vanishes by the proved
immersion inverse, and the kernel coordinate exponentiates to the original
stabilizer element. No subgroup manifold theorem is assumed. -/

noncomputable section
namespace BanachIsometric.StabilizerLieCoordinates
open Set Filter
open scoped Topology NNReal

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem exponential_coordinates (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∀ᶠ R : unitaryRepresentationStabilizer ρ v in 𝓝 1,
      exponential ρ v horbit (coordinates ρ v R) = R := by
  let H := unitaryRepresentationStabilizer ρ v
  let U := complement ρ v
  let K := kernel ρ v
  let hc := complement_isCompl ρ v
  let D := derivative ρ v
  let e := UnitaryOrbit.exponential A U
  let DP : U →L[ℝ] W := D.comp U.subtypeL
  have hF := expOrbit_hasStrictFDerivAt_zero ρ v horbit
  have hDP : HasStrictFDerivAt (fun x : U => ρ (e x : A) v) DP 0 :=
    hF.comp 0 (UnitaryOrbit.inclusion A U).hasStrictFDerivAt
  have hDinj : Function.Injective DP := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hmem : x.val - y.val ∈ U ⊓ K := by
      refine ⟨U.sub_mem x.property y.property, ?_⟩
      change D (x.val - y.val) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    rw [hc.inf_eq_bot] at hmem
    exact hmem
  obtain ⟨g, B, hB, _, _, _, hg0, _, hgInv, _⟩ :=
    exists_lipschitz_inverse_of_injective_strictDerivative
      (fun x : U => ρ (e x : A) v) DP hDP hDinj
  have he0 : ρ (e 0 : A) v = v := by
    dsimp only [e]
    rw [UnitaryOrbit.exponential_zero]
    change ρ (1 : A) v = v
    rw [map_one]
    rfl
  rw [he0] at hg0
  let z : H → U × K := fun R => SkewFactorization.coordinates A U K hc ((R : unitary A) : A)
  have hval : ContinuousAt (fun R : H => ((R : unitary A) : A)) 1 :=
    continuous_subtype_val.continuousAt.comp continuous_subtype_val.continuousAt
  have hzA : ContinuousAt (SkewFactorization.coordinates A U K hc) (1 : A) :=
    (SkewFactorization.coordinates_hasStrictFDerivAt A U K hc).continuousAt
  have hz : ContinuousAt z 1 := by
    exact hzA.comp_of_eq hval rfl
  have hz0 : z 1 = 0 := by simp [z]
  have hsmall : ∀ᶠ R : H in 𝓝 1, (z R).1 ∈ B := by
    apply (continuous_fst.continuousAt.comp hz).tendsto.eventually
    simpa only [Function.comp_apply, hz0, Prod.fst_zero] using hB
  have hfac : ∀ᶠ R : H in 𝓝 1,
      SkewFactorization.expProduct A U K (z R) = ((R : unitary A) : A) := by
    have h := hval.tendsto.eventually (SkewFactorization.expProduct_coordinates A U K hc)
    filter_upwards [h] with R hR
    exact hR (R : unitary A).property
  filter_upwards [hsmall, hfac] with R hRsmall hRfac
  have hY : fderiv ℝ (expOrbit ρ v) 0 (((z R).2 : UnitaryOrbit.Skew A) : A) = 0 := (z R).2.property
  have hfixed (t : ℝ) :
      ρ (NormedSpace.exp ℝ (t • (((z R).2 : UnitaryOrbit.Skew A) : A))) v = v :=
    representation_exp_fixed_of_fderiv_eq_zero ρ v hF.differentiableAt _ hY t
  have hOrbitX : ρ (e (z R).1 : A) v = v := by
    have hRmem : ρ (((R : unitary A) : A)) v = v := R.property
    rw [← hRfac] at hRmem
    change ρ (NormedSpace.exp ℝ (((z R).1 : UnitaryOrbit.Skew A) : A) *
      NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A)) v = v at hRmem
    rw [map_mul] at hRmem
    change ρ (e (z R).1 : A)
      (ρ (NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A)) v) = v at hRmem
    have hfixed1 : ρ (NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A)) v = v := by
      simpa only [one_smul] using hfixed 1
    rwa [hfixed1] at hRmem
  have hX : (z R).1 = 0 := by
    have h := hgInv (z R).1 hRsmall
    rw [hOrbitX, hg0] at h
    exact h.symm
  have hExpY : NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A) =
      ((R : unitary A) : A) := by
    change NormedSpace.exp ℝ (((z R).1 : UnitaryOrbit.Skew A) : A) *
      NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A) = _ at hRfac
    rw [hX] at hRfac
    simpa only [Submodule.coe_zero, NormedSpace.exp_zero, one_mul] using hRfac
  apply Subtype.ext
  apply Subtype.ext
  exact hExpY

end BanachIsometric.StabilizerLieCoordinates
