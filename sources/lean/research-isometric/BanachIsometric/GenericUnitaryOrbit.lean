import BanachIsometric.SkewFactorization
import BanachIsometric.CompactOrbitSlice
import BanachIsometric.InfinitesimalStabilizer
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# A local Lipschitz section of an actual unitary representation orbit

The complement to the kernel of the actual orbit derivative is constructed
algebraically. Its exponential patch has injective derivative. The complementary
kernel exponentiates to stabilizers, by differentiating the one-parameter action.
Local skew factorisation and compactness then supply a section of the orbit.
-/

namespace BanachIsometric

open Filter Set
open scoped Topology NNReal

noncomputable section

namespace UnitaryOrbit

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A]

abbrev Skew := SkewFactorization.Space A

def inclusion (U : Submodule ℝ (Skew A)) : U →L[ℝ] A :=
  (skewAdjoint.submodule ℝ A).subtypeL.comp U.subtypeL

def exponential (U : Submodule ℝ (Skew A)) (x : U) : unitary A :=
  ⟨NormedSpace.exp ℝ (inclusion A U x),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ x.val.property⟩

@[simp] theorem exponential_zero (U : Submodule ℝ (Skew A)) : exponential A U 0 = 1 := by
  apply Subtype.ext
  simp [exponential]

theorem exponential_hasStrictFDerivAt (U : Submodule ℝ (Skew A)) :
    HasStrictFDerivAt (fun x : U => (exponential A U x : A)) (inclusion A U) 0 := by
  have h : HasStrictFDerivAt (NormedSpace.exp ℝ : A → A) (ContinuousLinearMap.id ℝ A)
      (inclusion A U (0 : U)) := by
    simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
  simpa only [ContinuousLinearMap.id_comp] using h.comp 0 (inclusion A U).hasStrictFDerivAt

theorem exponential_lipschitzOn_nhds (U : Submodule ℝ (Skew A)) :
    ∃ T ∈ 𝓝 (0 : U), ∃ L : ℝ≥0, LipschitzOnWith L (exponential A U) T := by
  obtain ⟨T, hT, happ⟩ := (exponential_hasStrictFDerivAt A U).approximates_deriv_on_nhds
    (c := 1) (Or.inr zero_lt_one)
  refine ⟨T, hT, ‖inclusion A U‖₊ + 1, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact happ.lipschitz.dist_le_mul (⟨x, hx⟩ : T) (⟨y, hy⟩ : T)

end UnitaryOrbit

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [CompactSpace (unitary A)]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- A local Lipschitz section for the actual orbit of a finite-dimensional
continuous linear representation of a compact unitary group. Smoothness is
required only of the actual ambient orbit map. No stabilizer, factorisation,
quotient, or local-section conclusion occurs among the premises. -/
theorem exists_lipschitz_unitary_orbit_section
    (ρ : A →* Module.End ℝ W)
    (hρ : Continuous (fun p : A × W => ρ p.1 p.2))
    (v : W) (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∃ s : W → unitary A, ∃ N ∈ 𝓝 v, ∃ L : ℝ≥0,
      s v = 1 ∧ LipschitzOnWith L s N ∧
      ∀ y ∈ N, (∃ R : unitary A, ρ (R : A) v = y) → ρ (s y : A) v = y := by
  classical
  letI : MulAction (unitary A) W :=
    { smul := fun R w => ρ (R : A) w
      one_smul := by intro w; change ρ (1 : A) w = w; rw [map_one]; rfl
      mul_smul := by
        intro R S w
        change ρ ((R : A) * (S : A)) w = ρ (R : A) (ρ (S : A) w)
        rw [map_mul]
        rfl }
  letI : ContinuousSMul (unitary A) W :=
    ⟨hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
  let F : A → W := fun X => ρ (NormedSpace.exp ℝ X) v
  have hF : HasStrictFDerivAt F (fderiv ℝ F 0) 0 := by
    have hO : HasStrictFDerivAt (fun R : A => ρ R v)
        (fderiv ℝ (fun R : A => ρ R v) 1) (NormedSpace.exp ℝ (0 : A)) := by
      simpa only [NormedSpace.exp_zero] using
        (horbit.hasStrictFDerivAt (x := (1 : A)) (by simp))
    have h := hO.comp (0 : A) (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
    change HasStrictFDerivAt F _ 0 at h
    rw [h.hasFDerivAt.fderiv]
    exact h
  let D : UnitaryOrbit.Skew A →L[ℝ] W :=
    (fderiv ℝ F 0).comp (skewAdjoint.submodule ℝ A).subtypeL
  let V : Submodule ℝ (UnitaryOrbit.Skew A) := LinearMap.ker D.toLinearMap
  obtain ⟨U, hVU⟩ := V.exists_isCompl
  have hc : IsCompl U V := hVU.symm
  let e : U → unitary A := UnitaryOrbit.exponential A U
  let DP : U →L[ℝ] W := D.comp U.subtypeL
  have hDP : HasStrictFDerivAt (fun x : U => e x • v) DP 0 := by
    have h := hF.comp 0 (UnitaryOrbit.inclusion A U).hasStrictFDerivAt
    exact h
  have hDinj : Function.Injective DP := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hmem : x.val - y.val ∈ U ⊓ V := by
      refine ⟨U.sub_mem x.property y.property, ?_⟩
      change D (x.val - y.val) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    rw [hc.inf_eq_bot] at hmem
    exact hmem
  let c : unitary A → U := fun R =>
    (SkewFactorization.coordinates A U V hc (R : A)).1
  have hc0 : c 1 = 0 := by simp [c]
  have hval : ContinuousAt (fun R : unitary A => (R : A)) 1 :=
    continuous_subtype_val.continuousAt
  have hcCont : ContinuousAt c 1 := by
    have hz := (SkewFactorization.coordinates_hasStrictFDerivAt A U V hc).continuousAt
    have hz' : ContinuousAt (fun R : A => (SkewFactorization.coordinates A U V hc R).1) 1 :=
      continuous_fst.continuousAt.comp hz
    exact hz'.comp (f := fun R : unitary A => (R : A)) hval
  have hcover : ∀ᶠ R : unitary A in 𝓝 1, e (c R) • v = R • v := by
    have hfac : ∀ᶠ R : unitary A in 𝓝 1,
        (R : A) ∈ unitary A →
          SkewFactorization.expProduct A U V
            (SkewFactorization.coordinates A U V hc (R : A)) = (R : A) :=
      hval.tendsto.eventually
        (SkewFactorization.expProduct_coordinates A U V hc)
    filter_upwards [hfac] with R hR
    let z := SkewFactorization.coordinates A U V hc (R : A)
    have hy : fderiv ℝ F 0 ((z.2 : UnitaryOrbit.Skew A) : A) = 0 := z.2.property
    have hfix : ρ (NormedSpace.exp ℝ ((z.2 : UnitaryOrbit.Skew A) : A)) v = v := by
      simpa only [one_smul] using representation_exp_fixed_of_fderiv_eq_zero ρ v
        hF.differentiableAt ((z.2 : UnitaryOrbit.Skew A) : A) hy 1
    change ρ (e (c R) : A) v = ρ (R : A) v
    rw [← hR R.property]
    change ρ (NormedSpace.exp ℝ ((z.1 : UnitaryOrbit.Skew A) : A)) v =
      ρ (NormedSpace.exp ℝ ((z.1 : UnitaryOrbit.Skew A) : A) *
        NormedSpace.exp ℝ ((z.2 : UnitaryOrbit.Skew A) : A)) v
    rw [map_mul]
    change _ = ρ (NormedSpace.exp ℝ ((z.1 : UnitaryOrbit.Skew A) : A))
      (ρ (NormedSpace.exp ℝ ((z.2 : UnitaryOrbit.Skew A) : A)) v)
    rw [hfix]
  exact exists_lipschitz_orbit_section_of_local_factorization v e
    (UnitaryOrbit.exponential_zero A U) c hc0 hcCont hcover DP hDP hDinj
    (UnitaryOrbit.exponential_lipschitzOn_nhds A U)

end
end BanachIsometric
