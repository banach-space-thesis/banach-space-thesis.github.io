import ThesisCommon.Analysis.LpHaarDyadicCoefficient
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! The finite Haar levels are linearly independent and have explicitly
constructed continuous projections on the actual interval Lp spaces. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical BigOperators
namespace ThesisCommon

theorem lpHaarDyadic_level_linearIndependent (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (n : ℕ) :
    LinearIndependent 𝕜 (fun k : Fin (2 ^ n) => lpHaarDyadic 𝕜 p n k) := by
  apply Fintype.linearIndependent_iffₛ.mpr
  intro a b hab k
  have h := congrArg (lpHaarDyadicCoefficient 𝕜 p n k) hab
  simpa only [map_sum, map_smul, lpHaarDyadicCoefficient_apply_level,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] using h

def lpHaarLevelProjection (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n : ℕ) :
    IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  ∑ k : Fin (2 ^ n), (lpHaarDyadicCoefficient 𝕜 p n k).smulRight (lpHaarDyadic 𝕜 p n k)

theorem lpHaarLevelProjection_apply (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarLevelProjection 𝕜 p n f =
      ∑ k : Fin (2 ^ n), lpHaarDyadicCoefficient 𝕜 p n k f • lpHaarDyadic 𝕜 p n k := by
  simp [lpHaarLevelProjection, ContinuousLinearMap.sum_apply]

theorem lpHaarLevelProjection_coefficient (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (n : ℕ) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicCoefficient 𝕜 p n k (lpHaarLevelProjection 𝕜 p n f) =
      lpHaarDyadicCoefficient 𝕜 p n k f := by
  rw [lpHaarLevelProjection_apply]
  simp only [map_sum, map_smul, lpHaarDyadicCoefficient_apply_level,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

theorem lpHaarLevelProjection_fix (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (n : ℕ) (j : Fin (2 ^ n)) :
    lpHaarLevelProjection 𝕜 p n (lpHaarDyadic 𝕜 p n j) = lpHaarDyadic 𝕜 p n j := by
  rw [lpHaarLevelProjection_apply]
  simp only [lpHaarDyadicCoefficient_apply_level, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem lpHaarLevelProjection_idempotent (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (n : ℕ) :
    (lpHaarLevelProjection 𝕜 p n).comp (lpHaarLevelProjection 𝕜 p n) =
      lpHaarLevelProjection 𝕜 p n := by
  apply ContinuousLinearMap.ext
  intro f
  change lpHaarLevelProjection 𝕜 p n (lpHaarLevelProjection 𝕜 p n f) = _
  rw [lpHaarLevelProjection_apply]
  simp only [lpHaarLevelProjection_coefficient]
  exact (lpHaarLevelProjection_apply 𝕜 p n f).symm

theorem lpHaarLevelProjection_mem_span (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarLevelProjection 𝕜 p n f ∈
      Submodule.span 𝕜 (Set.range (fun k : Fin (2 ^ n) => lpHaarDyadic 𝕜 p n k)) := by
  rw [lpHaarLevelProjection_apply]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem lpHaarLevelProjection_range (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (n : ℕ) :
    LinearMap.range (lpHaarLevelProjection 𝕜 p n).toLinearMap =
      Submodule.span 𝕜 (Set.range (fun k : Fin (2 ^ n) => lpHaarDyadic 𝕜 p n k)) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact lpHaarLevelProjection_mem_span 𝕜 p n f
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact ⟨lpHaarDyadic 𝕜 p n k, lpHaarLevelProjection_fix 𝕜 p n k⟩

end ThesisCommon
