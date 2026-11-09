import BanachIsometric.ExponentialLocal
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Local exponential factorisation along complementary skew subspaces

The inverse function theorem is applied to the skew part of
`log (exp X * exp Y)`. Its derivative at zero is the addition equivalence of
the complementary subspaces. This constructs actual local coordinates;
factorisation is not assumed as an orbit-slice or closed-subgroup theorem.
-/

namespace BanachIsometric
namespace SkewFactorization

open Filter Set
open scoped Topology NNReal RightActions

noncomputable section

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

abbrev Space (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [StarRing A]
    [StarModule ℝ A] := ↥(skewAdjoint.submodule ℝ A)

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [StarRing A]
  [StarModule ℝ A] [ContinuousStar A]

def projection : A →L[ℝ] Space A := skewAdjointPartL ℝ A

theorem projection_subtype (x : Space A) : projection A (x : A) = x :=
  DFunLike.congr_fun (skewAdjointPart_comp_subtype_skewAdjoint ℝ (A := A)) x

theorem coe_projection_of_mem {x : A} (hx : x ∈ skewAdjoint A) :
    (projection A x : A) = x :=
  congrArg Subtype.val (projection_subtype A ⟨x, hx⟩)

variable (U V : Submodule ℝ (Space A))

def firstInclusion : (U × V) →L[ℝ] A :=
  ((skewAdjoint.submodule ℝ A).subtypeL.comp U.subtypeL).comp
    (ContinuousLinearMap.fst ℝ U V)

def secondInclusion : (U × V) →L[ℝ] A :=
  ((skewAdjoint.submodule ℝ A).subtypeL.comp V.subtypeL).comp
    (ContinuousLinearMap.snd ℝ U V)

variable [CompleteSpace A]

def expProduct (z : U × V) : A :=
  NormedSpace.exp ℝ (firstInclusion A U V z) *
    NormedSpace.exp ℝ (secondInclusion A U V z)

omit [ContinuousStar A] [CompleteSpace A] in
@[simp] theorem expProduct_zero : expProduct A U V 0 = 1 := by simp [expProduct]

theorem expProduct_mem_unitary (z : U × V) : expProduct A U V z ∈ unitary A := by
  exact (unitary A).mul_mem
    (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ z.1.val.property)
    (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ z.2.val.property)

omit [ContinuousStar A] in
theorem expProduct_hasStrictFDerivAt :
    HasStrictFDerivAt (expProduct A U V) (firstInclusion A U V + secondInclusion A U V) 0 := by
  have hexp := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)
  have hx : HasStrictFDerivAt (fun z : U × V => NormedSpace.exp ℝ (firstInclusion A U V z))
      (firstInclusion A U V) 0 := by
    have hh : HasStrictFDerivAt (NormedSpace.exp ℝ : A → A) (ContinuousLinearMap.id ℝ A)
        (firstInclusion A U V (0 : U × V)) := by simpa using hexp
    simpa only [ContinuousLinearMap.id_comp] using
      hh.comp 0 (firstInclusion A U V).hasStrictFDerivAt
  have hy : HasStrictFDerivAt (fun z : U × V => NormedSpace.exp ℝ (secondInclusion A U V z))
      (secondInclusion A U V) 0 := by
    have hh : HasStrictFDerivAt (NormedSpace.exp ℝ : A → A) (ContinuousLinearMap.id ℝ A)
        (secondInclusion A U V (0 : U × V)) := by simpa using hexp
    simpa only [ContinuousLinearMap.id_comp] using
      hh.comp 0 (secondInclusion A U V).hasStrictFDerivAt
  convert hx.fun_mul' hy using 1
  apply ContinuousLinearMap.ext
  intro z
  simp [add_comm]

def factorMap (z : U × V) : Space A :=
  projection A (localAlgebraLog A (expProduct A U V z))

@[simp] theorem factorMap_zero : factorMap A U V 0 = 0 := by
  simp [factorMap, localAlgebraLog_one]

def logarithmicSkew (R : A) : Space A := projection A (localAlgebraLog A R)

@[simp] theorem logarithmicSkew_one : logarithmicSkew A 1 = 0 := by
  simp [logarithmicSkew, localAlgebraLog_one]

theorem logarithmicSkew_hasStrictFDerivAt :
    HasStrictFDerivAt (logarithmicSkew A) (projection A) 1 := by
  simpa only [ContinuousLinearMap.comp_id] using
    (projection A).hasStrictFDerivAt.comp 1 (localAlgebraLog_hasStrictFDerivAt A)

variable [FiniteDimensional ℝ A]

def additionEquiv (hc : IsCompl U V) : (U × V) ≃L[ℝ] Space A :=
  (U.prodEquivOfIsCompl V hc).toContinuousLinearEquiv

theorem factorMap_hasStrictFDerivAt (hc : IsCompl U V) :
    HasStrictFDerivAt (factorMap A U V) (additionEquiv A U V hc : (U × V) →L[ℝ] Space A) 0 := by
  have hlog : HasStrictFDerivAt (localAlgebraLog A) (ContinuousLinearMap.id ℝ A)
      (expProduct A U V 0) := by
    simpa only [expProduct_zero] using localAlgebraLog_hasStrictFDerivAt A
  have hcomp := (projection A).hasStrictFDerivAt.comp 0
    (hlog.comp 0 (expProduct_hasStrictFDerivAt A U V))
  have hder : (projection A).comp
      ((ContinuousLinearMap.id ℝ A).comp (firstInclusion A U V + secondInclusion A U V)) =
        (additionEquiv A U V hc : (U × V) →L[ℝ] Space A) := by
    apply ContinuousLinearMap.ext
    intro z
    change projection A ((z.1.val : A) + (z.2.val : A)) = z.1.val + z.2.val
    rw [map_add, projection_subtype, projection_subtype]
  rw [hder] at hcomp
  exact hcomp

def localInverse (hc : IsCompl U V) : Space A → U × V :=
  (factorMap_hasStrictFDerivAt A U V hc).localInverse (factorMap A U V)
    (additionEquiv A U V hc) 0

@[simp] theorem localInverse_zero (hc : IsCompl U V) : localInverse A U V hc 0 = 0 := by
  simpa only [factorMap_zero, localInverse] using
    (factorMap_hasStrictFDerivAt A U V hc).localInverse_apply_image

theorem factorMap_localInverse (hc : IsCompl U V) :
    ∀ᶠ z : Space A in 𝓝 0, factorMap A U V (localInverse A U V hc z) = z := by
  simpa only [factorMap_zero, localInverse] using
    (factorMap_hasStrictFDerivAt A U V hc).eventually_right_inverse

theorem localInverse_hasStrictFDerivAt (hc : IsCompl U V) :
    HasStrictFDerivAt (localInverse A U V hc)
      ((additionEquiv A U V hc).symm : Space A →L[ℝ] U × V) 0 := by
  simpa only [factorMap_zero, localInverse] using
    (factorMap_hasStrictFDerivAt A U V hc).to_localInverse

def coordinates (hc : IsCompl U V) (R : A) : U × V :=
  localInverse A U V hc (logarithmicSkew A R)

@[simp] theorem coordinates_one (hc : IsCompl U V) : coordinates A U V hc 1 = 0 := by
  simp [coordinates]

theorem coordinates_hasStrictFDerivAt (hc : IsCompl U V) :
    HasStrictFDerivAt (coordinates A U V hc)
      (((additionEquiv A U V hc).symm : Space A →L[ℝ] U × V).comp (projection A)) 1 := by
  have hh : HasStrictFDerivAt (localInverse A U V hc)
      ((additionEquiv A U V hc).symm : Space A →L[ℝ] U × V) (logarithmicSkew A 1) := by
    simpa only [logarithmicSkew_one] using localInverse_hasStrictFDerivAt A U V hc
  exact hh.comp 1 (logarithmicSkew_hasStrictFDerivAt A)

theorem coordinates_lipschitzOn_nhds (hc : IsCompl U V) :
    ∃ N ∈ 𝓝 (1 : A), ∃ L : ℝ≥0, LipschitzOnWith L (coordinates A U V hc) N := by
  obtain ⟨N, hN, happrox⟩ :=
    (coordinates_hasStrictFDerivAt A U V hc).approximates_deriv_on_nhds
      (c := 1) (Or.inr zero_lt_one)
  refine ⟨N, hN,
    ‖((additionEquiv A U V hc).symm : Space A →L[ℝ] U × V).comp (projection A)‖₊ + 1, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact happrox.lipschitz.dist_le_mul (⟨x, hx⟩ : N) (⟨y, hy⟩ : N)

/-- The locally constructed coordinates give an exact product for every
unitary sufficiently close to the identity. -/
theorem expProduct_coordinates (hc : IsCompl U V) :
    ∀ᶠ R : A in 𝓝 1, R ∈ unitary A →
      expProduct A U V (coordinates A U V hc R) = R := by
  have hk : Tendsto (logarithmicSkew A) (𝓝 (1 : A)) (𝓝 0) := by
    simpa only [logarithmicSkew_one] using
      (logarithmicSkew_hasStrictFDerivAt A).continuousAt.tendsto
  have hz : Tendsto (coordinates A U V hc) (𝓝 (1 : A)) (𝓝 0) := by
    simpa only [coordinates_one] using
      (coordinates_hasStrictFDerivAt A U V hc).continuousAt.tendsto
  have hm : Tendsto (fun R : A => expProduct A U V (coordinates A U V hc R))
      (𝓝 1) (𝓝 1) := by
    simpa only [Function.comp_apply, expProduct_zero] using
      (expProduct_hasStrictFDerivAt A U V).continuousAt.tendsto.comp hz
  filter_upwards [hk.eventually (factorMap_localInverse A U V hc),
    exp_localAlgebraLog A, hm.eventually (exp_localAlgebraLog A),
    unitary_iff_localAlgebraLog_skew A, hm.eventually (unitary_iff_localAlgebraLog_skew A)]
    with R hinv hExpR hExpP hskR hskP hunit
  have hproj : projection A (localAlgebraLog A (expProduct A U V (coordinates A U V hc R))) =
      projection A (localAlgebraLog A R) := hinv
  have hlog : localAlgebraLog A (expProduct A U V (coordinates A U V hc R)) =
      localAlgebraLog A R := by
    calc
      _ = (projection A (localAlgebraLog A
          (expProduct A U V (coordinates A U V hc R))) : A) :=
        (coe_projection_of_mem A (hskP.mp
          (expProduct_mem_unitary A U V (coordinates A U V hc R)))).symm
      _ = (projection A (localAlgebraLog A R) : A) := congrArg Subtype.val hproj
      _ = localAlgebraLog A R := coe_projection_of_mem A (hskR.mp hunit)
  calc
    expProduct A U V (coordinates A U V hc R) =
        NormedSpace.exp ℝ (localAlgebraLog A (expProduct A U V (coordinates A U V hc R))) :=
      hExpP.symm
    _ = NormedSpace.exp ℝ (localAlgebraLog A R) := congrArg (NormedSpace.exp ℝ) hlog
    _ = R := hExpR

/-- Actual locally Lipschitz factors in the specified complementary real
skew-adjoint subspaces. The functions are zero at the identity, and their
exponentials multiply to the original unitary near the identity. -/
theorem exists_local_factors (hc : IsCompl U V) :
    ∃ X : A → U, ∃ Y : A → V, X 1 = 0 ∧ Y 1 = 0 ∧
      (∃ N ∈ 𝓝 (1 : A), ∃ L : ℝ≥0,
        LipschitzOnWith L X N ∧ LipschitzOnWith L Y N) ∧
      ∀ᶠ R : A in 𝓝 1, R ∈ unitary A →
        NormedSpace.exp ℝ ((X R : Space A) : A) *
          NormedSpace.exp ℝ ((Y R : Space A) : A) = R := by
  let X : A → U := fun R => (coordinates A U V hc R).1
  let Y : A → V := fun R => (coordinates A U V hc R).2
  refine ⟨X, Y, ?_, ?_, ?_, ?_⟩
  · simp [X]
  · simp [Y]
  · obtain ⟨N, hN, L, hL⟩ := coordinates_lipschitzOn_nhds A U V hc
    refine ⟨N, hN, L, ?_, ?_⟩
    · apply LipschitzOnWith.of_dist_le_mul
      intro R hR S hS
      have hfst : dist (X R) (X S) ≤ dist (coordinates A U V hc R) (coordinates A U V hc S) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      exact hfst.trans (hL.dist_le_mul R hR S hS)
    · apply LipschitzOnWith.of_dist_le_mul
      intro R hR S hS
      have hsnd : dist (Y R) (Y S) ≤ dist (coordinates A U V hc R) (coordinates A U V hc S) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      exact hsnd.trans (hL.dist_le_mul R hR S hS)
  · exact expProduct_coordinates A U V hc

end
end SkewFactorization
end BanachIsometric
