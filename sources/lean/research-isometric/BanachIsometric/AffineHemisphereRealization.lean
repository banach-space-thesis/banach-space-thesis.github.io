import BanachIsometric.AffineRationalCone
import BanachIsometric.HemisphereContraction
import BanachIsometric.ExactSectionHemisphere
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! Projective realization of affine chains carried by a closed hemisphere.
An admissible simplex has nonzero affine vectors and nonnegative pole inner
product. The realization commutes with every face of an admissible simplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric NormedSpace
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def affineHemisphereAdmissible {n : ℕ} (pole : sphere (0 : V) 1) (vertices : Fin (n + 1) → V) : Prop :=
  ∀ w, affineSingularSimplex vertices w ≠ 0 ∧ 0 ≤ inner ℝ pole.val (affineSingularSimplex vertices w)

private def affineHemisphereSimplexOfAdmissible {n : ℕ} (pole : sphere (0 : V) 1)
    (vertices : Fin (n + 1) → V) (h : affineHemisphereAdmissible pole vertices) :
    RawSingularSimplex (closedHemisphere pole) n where
  toFun w := ⟨⟨normalize (affineSingularSimplex vertices w),
      mem_sphere_zero_iff_norm.mpr (norm_normalize (h w).1)⟩, by
    change 0 ≤ inner ℝ pole.val (normalize (affineSingularSimplex vertices w))
    rw [NormedSpace.normalize, real_inner_smul_right]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (h w).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact ((affineSingularSimplex vertices).continuous.norm.inv₀
      (fun w => norm_ne_zero_iff.mpr (h w).1)).smul (affineSingularSimplex vertices).continuous

def affineHemisphereSimplex {n : ℕ} (pole : sphere (0 : V) 1) (vertices : Fin (n + 1) → V) :
    RawSingularSimplex (closedHemisphere pole) n := by
  classical
  exact if h : affineHemisphereAdmissible pole vertices then affineHemisphereSimplexOfAdmissible pole vertices h
    else ContinuousMap.const (Simplex n) (hemispherePole pole)

theorem affineHemisphereSimplex_val {n : ℕ} (pole : sphere (0 : V) 1) (vertices : Fin (n + 1) → V)
    (h : affineHemisphereAdmissible pole vertices) (w : Simplex n) :
    (affineHemisphereSimplex pole vertices w).val.val = normalize (affineSingularSimplex vertices w) := by
  classical
  rw [affineHemisphereSimplex, dif_pos h]
  rfl

theorem affineHemisphereAdmissible_precomp {a b : ℕ} (pole : sphere (0 : V) 1)
    (vertices : Fin (b + 1) → V) (f : Fin (a + 1) → Fin (b + 1))
    (h : affineHemisphereAdmissible pole vertices) : affineHemisphereAdmissible pole (vertices ∘ f) := by
  intro w
  have hw := ContinuousMap.congr_fun (affineSingularSimplex_precomp f vertices) w
  change affineSingularSimplex vertices (simplexMap f w) = affineSingularSimplex (vertices ∘ f) w at hw
  rw [← hw]
  exact h (simplexMap f w)

theorem affineHemisphereSimplex_precomp {a b : ℕ} (pole : sphere (0 : V) 1)
    (vertices : Fin (b + 1) → V) (f : Fin (a + 1) → Fin (b + 1))
    (h : affineHemisphereAdmissible pole vertices) :
    (affineHemisphereSimplex pole vertices).comp (simplexMap f) = affineHemisphereSimplex pole (vertices ∘ f) := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  apply Subtype.ext
  change (affineHemisphereSimplex pole vertices (simplexMap f w)).val.val =
    (affineHemisphereSimplex pole (vertices ∘ f) w).val.val
  rw [affineHemisphereSimplex_val pole vertices h,
    affineHemisphereSimplex_val pole (vertices ∘ f) (affineHemisphereAdmissible_precomp pole vertices f h)]
  have hw := ContinuousMap.congr_fun (affineSingularSimplex_precomp f vertices) w
  have hn := congrArg (NormedSpace.normalize : V → V) hw
  exact hn

def affineHemisphereRealization (pole : sphere (0 : V) 1) (n : ℕ) :
    AffineRationalChains V n →ₗ[ℚ] RawRationalChains (closedHemisphere pole) n :=
  Finsupp.lmapDomain ℚ ℚ (affineHemisphereSimplex pole)

theorem affineHemisphereRealization_single (pole : sphere (0 : V) 1) (n : ℕ)
    (vertices : Fin (n + 1) → V) (a : ℚ) :
    affineHemisphereRealization pole n (Finsupp.single vertices a) =
      Finsupp.single (affineHemisphereSimplex pole vertices) a := by
  simp only [affineHemisphereRealization, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem affineHemisphereRealization_boundary_single (pole : sphere (0 : V) 1) (n : ℕ)
    (vertices : Fin (n + 2) → V) (a : ℚ) (h : affineHemisphereAdmissible pole vertices) :
    rawBoundary n (affineHemisphereRealization pole (n + 1) (Finsupp.single vertices a)) =
      affineHemisphereRealization pole n (affineBoundary n (Finsupp.single vertices a)) := by
  rw [affineHemisphereRealization_single, rawBoundary_single, affineBoundary_single, map_sum]
  simp only [map_zsmul, affineHemisphereRealization_single]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (affineHemisphereSimplex pole vertices).comp (face i) =
    affineHemisphereSimplex pole (vertices ∘ i.succAbove) from
      affineHemisphereSimplex_precomp pole vertices i.succAbove h]

theorem affineHemisphereRealization_boundary (pole : sphere (0 : V) 1) (n : ℕ)
    (c : AffineRationalChains V (n + 1))
    (hc : c ∈ Finsupp.supported ℚ ℚ {vertices | affineHemisphereAdmissible pole vertices}) :
    rawBoundary n (affineHemisphereRealization pole (n + 1) c) =
      affineHemisphereRealization pole n (affineBoundary n c) := by
  let D := (rawBoundary n).comp (affineHemisphereRealization pole (n + 1)) -
    (affineHemisphereRealization pole n).comp (affineBoundary n)
  have h : Finsupp.supported ℚ ℚ {vertices | affineHemisphereAdmissible pole vertices} ≤ LinearMap.ker D := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨vertices, hvertices, rfl⟩
    exact sub_eq_zero.mpr (affineHemisphereRealization_boundary_single pole n vertices 1 hvertices)
  exact sub_eq_zero.mp (h hc)

end BanachIsometric.SingularPrism
