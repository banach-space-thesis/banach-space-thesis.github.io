/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Analysis.NormedSpace.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import NonCalkinAlgebra.CompactSpectralSupport

/-!
# Spectral theory of compact operators

This file develops the spectral theory of compact operators on Banach spaces.
The main result is the Fredholm alternative for compact operators.

## Main results

* `antilipschitz_of_not_hasEigenvalue`: if `T` is a compact operator and `μ ≠ 0` is not an
  eigenvalue, then `T - μI` is antilipschitz, i.e. bounded below.
* `hasEigenvalue_or_mem_resolventSet`: the Fredholm alternative for compact operators, which says
  that if `T` is a compact operator and `μ ≠ 0`, then either `μ` is an eigenvalue of `T`, or `μ`
  is in the resolvent set of `T`.
* `hasEigenvalue_iff_mem_spectrum`: if `T` is a compact operator, then the nonzero eigenvalues of
  `T` are exactly the nonzero points in the spectrum of `T`.

We follow the proof given in Section 2 of
https://terrytao.wordpress.com/2011/04/10/a-proof-of-the-fredholm-alternative/
but adapt it to work in a more general setting of spaces over nontrivially normed fields,
rather than just over `ℝ` or `ℂ`. The main technical hurdle is that we don't have the ability to
rescale vectors to have norm exactly `1`, so we have to work with vectors in a shell instead of on
the unit sphere, and this makes some of the intermediate statements more complicated.
-/


/-! Ported from mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.
The source and licence provenance are saved under source/mathlib-spectral.
Only compatibility changes for Lean 4.24 are made; no theorem is assumed. -/

namespace NonCalkinAlgebra.CompactSpectral

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {T : X →L[𝕜] X} {μ : 𝕜}

open Module End

theorem antilipschitzWith_iff_exists_mul_le_norm (f : X →L[𝕜] X) :
    (∃ K, AntilipschitzWith K f) ↔ ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖f x‖ := by
  constructor
  · rintro ⟨K, hK⟩
    have hpos : 0 < (K : ℝ) + 1 := by positivity
    refine ⟨1 / ((K : ℝ) + 1), div_pos one_pos hpos, ?_⟩
    intro x
    have hx : ‖x‖ ≤ ((K : ℝ) + 1) * ‖f x‖ :=
      (f.bound_of_antilipschitz hK x).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg (f x)))
    calc
      (1 / ((K : ℝ) + 1)) * ‖x‖ ≤
          (1 / ((K : ℝ) + 1)) * (((K : ℝ) + 1) * ‖f x‖) :=
        mul_le_mul_of_nonneg_left hx (le_of_lt (div_pos one_pos hpos))
      _ = ‖f x‖ := by rw [← mul_assoc, div_mul_cancel₀ 1 hpos.ne', one_mul]
  · rintro ⟨c, hc, hbound⟩
    refine ⟨⟨c⁻¹, inv_nonneg.mpr hc.le⟩, f.antilipschitz_of_bound ?_⟩
    intro x
    change ‖x‖ ≤ c⁻¹ * ‖f x‖
    calc
      ‖x‖ = c⁻¹ * (c * ‖x‖) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * ‖f x‖ := mul_le_mul_of_nonneg_left (hbound x) (inv_nonneg.mpr hc.le)

open Filter Topology in
/-- If `T : X →L[𝕜] X` is a compact operator on a Banach space `X`, and `μ ≠ 0` is not an
eigenvalue of `T`, then `T - μ • 1` is antilipschitz with positive constant.
That is, `T - μ • 1` is bounded below as an operator.

This is a useful step in the proof of the Fredholm alternative for compact operators. -/
theorem antilipschitz_of_not_hasEigenvalue (hT : IsCompactOperator T) (hμ : μ ≠ 0)
    (h : ¬ HasEigenvalue (T : End 𝕜 X) μ) :
    ∃ K, AntilipschitzWith K (T - μ • 1 : X →L[𝕜] X) := by
  -- Suppose not, and attempt to find an eigenvector with eigenvalue `μ`.
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  contrapose! h
  -- then for every `K > 0`, there is some `x` such that `‖(T - μ • 1) x‖ < K * ‖x‖`.
  replace hK : ∀ K > 0, ∃ x, ‖(T - μ • 1) x‖ < K * ‖x‖ := h
  -- In fact, there is a lower bound `c` such that for every `ε > 0`, there is an `x` with norm
  -- in the interval `[c, 1]` such that `‖(T - μ • 1) x‖ < ε`.
  -- (In the case of an `RCLike` field, where we can rescale, we could even get `‖x‖ = 1`, but we
  -- don't need that.)
  replace hK : ∃ c > 0, ∀ ε > 0, ∃ x, ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖(T - μ • 1) x‖ < ε := by
    obtain ⟨C, hC⟩ := NormedField.exists_one_lt_norm 𝕜
    refine ⟨‖C‖⁻¹, by positivity, fun ε hε ↦ ?_⟩
    obtain ⟨x, hx⟩ := hK ε (by positivity)
    have : x ≠ 0 := by aesop
    obtain ⟨η, hη, h₁, h₂, h₃⟩ := rescale_to_shell hC (ε := 1) (by simp) this
    refine ⟨η • x, h₁.le, by simpa using h₂, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * h₁
  obtain ⟨c, hc₀, hc⟩ := hK
  obtain ⟨φ, hφ_anti, hφ_pos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  -- Then find a sequence of vectors `xₙ` with norm in the interval `[c, 1]` such
  -- that `‖(T - μ • 1) xₙ‖ < φ n`, where `φ n` is a sequence of positive numbers tending to zero.
  have (n : ℕ) : ∃ x, ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖(T - μ • 1) x‖ < φ n := hc (φ n) (hφ_pos n)
  choose x hx_norm_upper hx_norm_lower hx_bound using this
  have hx_lim : Tendsto (fun n ↦ (T - μ • 1) (x n)) atTop (𝓝 0) := squeeze_zero_norm (by grind) hφ
  -- Define the sequence of vectors `yₙ := T xₙ`
  let y_ (n : ℕ) : X := T (x n)
  -- which are bounded away from zero.
  have hy_lower : ∃ d > 0, ∀ᶠ n in atTop, d ≤ ‖y_ n‖ := by
    refine ⟨(‖μ‖ * c) / 2, by positivity, ?_⟩
    filter_upwards [hφ.eventually_le_const (show (‖μ‖ * c) / 2 > 0 by positivity)] with n hn
    have h₁ : ‖T (x n) - μ • x n‖ < φ n := by simpa using hx_bound n
    have h₂ : ‖μ‖ * ‖x n‖ ≤ ‖T (x n)‖ + ‖T (x n) - μ • x n‖ := by
      simpa [norm_smul] using norm_le_norm_add_norm_sub (T (x n)) (μ • x n)
    linear_combination h₂ + h₁ + hn + ‖μ‖ * hx_norm_lower n
  -- The sequence `yₙ` is contained in the image of the closed unit ball under `T`,
  -- which is compact, since `T` is,
  -- so we can extract a convergent subsequence, and say `y_ (ψ n) → y`.
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (x := y_) (fun n ↦ hK' ⟨x n, by simp [*], rfl⟩)
  -- However `(T - μ • 1) yₙ = T ((T - μ • 1) xₙ) → 0`
  have hy_lim : Tendsto (fun n ↦ (T - μ • 1) (y_ n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using T.continuous.continuousAt.tendsto.comp hx_lim
  -- so `(T - μ • 1) y = 0`.
  have hy_eigen' : (T - μ • 1) y = 0 := by
    apply tendsto_nhds_unique _ (hy_lim.comp hψ.tendsto_atTop)
    have : Continuous (T - μ • 1 : X →L[𝕜] X) := by fun_prop
    exact this.continuousAt.tendsto.comp hψy
  -- Since `yₙ` are bounded away from `0`, we must have `y ≠ 0`.
  have hy_ne : y ≠ 0 := by
    obtain ⟨d, hd₀, hd⟩ := hy_lower
    rintro rfl
    suffices ∀ᶠ n : ℕ in atTop, False by rwa [eventually_const] at this
    have hnorm := hψy.norm
    simp only [norm_zero] at hnorm
    have hsmall : ∀ᶠ n in atTop, ‖y_ (ψ n)‖ < d := hnorm.eventually (gt_mem_nhds hd₀)
    filter_upwards [hψ.tendsto_atTop.eventually hd, hsmall] with n hlow hhigh
    exact hhigh.not_ge hlow
  -- So `y` is an eigenvector of `T` with eigenvalue `μ`,
  have : HasEigenvector (T : End 𝕜 X) μ y := by
    simpa [hasEigenvector_iff, mem_genEigenspace_one, hy_ne, sub_eq_zero] using hy_eigen'
  -- which is a contradiction.
  exact hasEigenvalue_of_hasEigenvector this

/--
Given an endomorphism `S` of a normed space that's a closed embedding but not surjective, we can
find a sequence of vectors `f n`, living inside a shell, such that `f n` is in the
range of `S ^ n` but is at least `1` away from any vector in the range of `S ^ (n + 1)`.
This is a useful construction for the proof of the Fredholm alternative for compact operators.
The conditions about `c` and `R` are to mimic those in Riesz's lemma.
-/
private theorem exists_seq {S : End 𝕜 X} (hS_not_surj : ¬ (S : X → X).Surjective)
    (hS_anti : Topology.IsClosedEmbedding S)
    {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) :
    ∃ f : ℕ → X,
      (∀ n, 1 ≤ ‖f n‖) ∧ (∀ n, ‖f n‖ ≤ R) ∧
      (∀ n, f n ∈ LinearMap.range (S ^ n)) ∧
      (∀ n, ∀ y ∈ LinearMap.range (S ^ (n + 1)), 1 ≤ ‖f n - y‖) :=
  CompactSpectralSupport.separation_sequence hS_not_surj hS_anti hc hR

variable [CompleteSpace X]

theorem operator_spectrum_eq (T : X →L[𝕜] X) :
    spectrum 𝕜 T = spectrum 𝕜 (T : End 𝕜 X) := by
  ext μ
  rw [spectrum.mem_iff, spectrum.mem_iff,
    ContinuousLinearMap.isUnit_iff_bijective, Module.End.isUnit_iff]
  rfl

/--
The **Fredholm alternative** for compact operators: if `T` is a compact operator and `μ ≠ 0`,
then either `μ` is an eigenvalue of `T`, or `μ` is in the resolvent set of `T`.
See also `hasEigenvalue_iff_mem_spectrum`, which says that the nonzero eigenvalues of a compact
operator are exactly the nonzero points in the spectrum of the operator.
-/
theorem hasEigenvalue_or_mem_resolventSet (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ∨ μ ∈ resolventSet 𝕜 T := by
  -- Suppose not, then `μ` is not an eigenvalue and is in the spectrum.
  by_contra!
  obtain ⟨h₁, h₂⟩ := this
  -- Defining S := `T - μ • 1`, we deduce that S is antilipschitz and not surjective.
  let S := T - μ • 1
  obtain ⟨K, hK : AntilipschitzWith K S⟩ := antilipschitz_of_not_hasEigenvalue hT hμ h₁
  replace h₂ : ¬ (S : X → X).Bijective := by
    rw [spectrum.mem_resolventSet_iff, ← IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at h₂
    convert h₂
    ext x
    simp [S]
  replace h₂ : ¬ (S : X → X).Surjective := fun hsurj => h₂ ⟨hK.injective, hsurj⟩
  -- Take a sequence of vectors `f n` in the range of `S ^ n` such that `‖f n‖` is in the
  -- interval `[1, ‖c‖ + 1]` and such that `f n` is at least `1` away from any vector in the range
  -- of `S ^ (n + 1)`.
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨f, hf_norm_lower, hf_norm_upper, hf_mem, hf_far⟩ := exists_seq h₂
    (hK.isClosedEmbedding S.uniformContinuous) hc (R := ‖c‖ + 1) (by simp)
  replace hf_mem {n m : ℕ} (h : m ≤ n) : f n ∈ LinearMap.range ((S : End 𝕜 X) ^ m) :=
    CompactSpectralSupport.range_powers_antitone (S : End 𝕜 X) h (hf_mem _)
  have hf_mem' {n m : ℕ} (h : m ≤ n) :
      S (f n) ∈ LinearMap.range ((S : End 𝕜 X) ^ (m + 1)) := by
    obtain ⟨y, hy⟩ := hf_mem h
    exact ⟨y, by rw [pow_succ', Module.End.mul_apply, hy]; rfl⟩
  -- Then the points `T (f n)` are bounded away from each other, using the separation property
  -- of the `f n` and the lower bound on their norms.
  have hlt (m n : ℕ) (hmn : m < n) : ‖μ‖ ≤ ‖T (f m) - T (f n)‖ := by
    let u : X := μ⁻¹ • (S (f n) - S (f m) + μ • f n)
    have hu : μ • (f m - u) = T (f m) - T (f n) := by
      rw [smul_sub, smul_inv_smul₀ hμ]
      simp [S]
      linear_combination (norm := module)
    have : u ∈ LinearMap.range ((S : End 𝕜 X) ^ (m + 1)) := by
      apply Submodule.smul_mem _ _ (Submodule.add_mem _ _ _)
      · exact Submodule.sub_mem _ (hf_mem' hmn.le) (hf_mem' le_rfl)
      · exact Submodule.smul_mem _ μ (hf_mem hmn)
    grw [← hu, norm_smul, mul_comm, ← hf_far _ u this, one_mul]
  have hp : Pairwise fun x₁ x₂ ↦ ‖μ‖ ≤ ‖T (f x₁) - T (f x₂)‖ := by
    intro m n hne
    rcases lt_or_gt_of_ne hne with hmn | hnm
    · exact hlt m n hmn
    · simpa only [norm_sub_rev] using hlt n m hnm
  -- However the `f n` are contained in a compact set, so their image under the compact operator `T`
  -- must contain a Cauchy subsequence, which is a contradiction.
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact (‖c‖ + 1)
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (fun n ↦ hK' ⟨f n, by simp [*], rfl⟩)
  replace hψy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hψy
  obtain ⟨N, hN⟩ := hψy ‖μ‖ (by positivity)
  have : ‖T (f (ψ (N + 1))) - T (f (ψ N))‖ < ‖μ‖ := by simpa [dist_eq_norm_sub] using hN (N + 1)
  refine this.not_ge (hp ?_)
  simp [hψ.injective.eq_iff]

/--
If `T` is a compact operator on a Banach space, then the nonzero eigenvalues of `T` are exactly
the nonzero points in the spectrum of `T`. This is a consequence of the Fredholm alternative for
compact operators. -/
theorem hasEigenvalue_iff_mem_spectrum (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ↔ μ ∈ spectrum 𝕜 T := by
  constructor
  · intro hμ'
    rw [operator_spectrum_eq T]
    exact hμ'.mem_spectrum
  · exact (hasEigenvalue_or_mem_resolventSet hT hμ).resolve_right

end
end NonCalkinAlgebra.CompactSpectral
