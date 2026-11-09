import PL1.WeakSchur
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Weak Cauchy sequences and bounded signed expansions in Schur spaces

These proofs give the bounded-completeness step in the paper's lattice lemma.
They do not assume or assert that an atomic lattice basis has already been constructed.
-/

noncomputable section
open Filter
open scoped Topology

namespace PL1.SchurBoundedCompleteness

section GeneralScalar

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Weak Cauchy convergence is tested against the entire continuous dual. -/
def WeaklyCauchy (x : ℕ → E) : Prop :=
  ∀ φ : E →L[𝕜] 𝕜, CauchySeq (fun n => φ (x n))

/-- A Schur space sends every weak Cauchy sequence to a norm Cauchy sequence. -/
theorem cauchySeq_of_weaklyCauchy (hS : HasSchurProperty 𝕜 E) {x : ℕ → E}
    (hx : WeaklyCauchy (𝕜 := 𝕜) x) : CauchySeq x := by
  by_contra hbad
  rw [Metric.cauchySeq_iff] at hbad
  push Not at hbad
  obtain ⟨ε, hε, hbad⟩ := hbad
  choose a ha b hb hab using hbad
  have hat : Tendsto a atTop atTop := tendsto_atTop_mono ha tendsto_id
  have hbt : Tendsto b atTop atTop := tendsto_atTop_mono hb tendsto_id
  have hweak : WeaklyConverges 𝕜 E (fun n => x (a n) - x (b n)) 0 := by
    intro φ
    obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete (hx φ)
    simpa only [map_sub, map_zero, sub_self, Function.comp_apply] using (hc.comp hat).sub (hc.comp hbt)
  have hn := (hS _ _ hweak).norm
  simp only [norm_zero] at hn
  have he := hn.eventually_lt_const hε
  obtain ⟨n, hn⟩ := he.exists
  exact (not_lt_of_ge (hab n)) (by simpa only [dist_eq_norm] using hn)

/-- Completeness upgrades weak Cauchy sequences in a Schur space to norm convergence. -/
theorem exists_tendsto_of_weaklyCauchy [CompleteSpace E] (hS : HasSchurProperty 𝕜 E)
    {x : ℕ → E} (hx : WeaklyCauchy (𝕜 := 𝕜) x) : ∃ a : E, Tendsto x atTop (𝓝 a) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_weaklyCauchy hS hx)

/-- In a complete Schur space, scalar summability against every continuous
functional forces genuine unordered vector summability. -/
theorem summable_of_dual_summable [CompleteSpace E] (hS : HasSchurProperty 𝕜 E)
    (x : ℕ → E) (hx : ∀ φ : E →L[𝕜] 𝕜, Summable (fun n => φ (x n))) : Summable x := by
  classical
  by_contra hbad
  rw [summable_iff_vanishing_norm] at hbad
  push Not at hbad
  obtain ⟨ε, hε, hbad⟩ := hbad
  choose t ht hnorm using fun n : ℕ => hbad (Finset.range n)
  have hweak : WeaklyConverges 𝕜 E (fun n => ∑ j ∈ t n, x j) 0 := by
    intro φ
    rw [map_zero]
    apply Metric.tendsto_atTop.mpr
    intro δ hδ
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 (hx φ) δ hδ
    obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
    refine ⟨N, fun n hn => ?_⟩
    simpa only [map_sum, dist_zero_right] using
      hs (t n) ((ht n).mono_right (hN.trans (Finset.range_mono hn)))
  have hz := (hS _ _ hweak).norm
  simp only [norm_zero] at hz
  obtain ⟨n, hn⟩ := (hz.eventually_lt_const hε).exists
  exact not_lt_of_ge (hnorm n) hn

end GeneralScalar

section RealScalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One bound for every finite initial signed sum. -/
def SignedSumsBounded (x : ℕ → E) (M : ℝ) : Prop :=
  ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, ε n = 1 ∨ ε n = -1) →
    ‖∑ n ∈ Finset.range N, ε n • x n‖ ≤ M

/-- Scalar signs can recover the entire finite sum of absolute dual values. -/
theorem sum_dual_norm_le_of_signed_sums_bounded (x : ℕ → E) (M : ℝ)
    (hM : SignedSumsBounded x M) (φ : E →L[ℝ] ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖φ (x n)‖) ≤ ‖φ‖ * M := by
  classical
  let ε : ℕ → ℝ := fun n => if 0 ≤ φ (x n) then 1 else -1
  have hε : ∀ n, ε n = 1 ∨ ε n = -1 := by intro n; dsimp [ε]; split <;> simp
  have heq : φ (∑ n ∈ Finset.range N, ε n • x n) =
      ∑ n ∈ Finset.range N, ‖φ (x n)‖ := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_smul]
    by_cases h : 0 ≤ φ (x n)
    · simp [ε, h, Real.norm_of_nonneg h]
    · simp [ε, h, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge h)]
  rw [← heq]
  calc
    _ ≤ ‖φ (∑ n ∈ Finset.range N, ε n • x n)‖ := le_abs_self _
    _ ≤ ‖φ‖ * ‖∑ n ∈ Finset.range N, ε n • x n‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * M := mul_le_mul_of_nonneg_left (hM N ε hε) (norm_nonneg _)

/-- Every continuous functional is absolutely summable on a series with bounded signed sums. -/
theorem dual_summable_norm_of_signed_sums_bounded (x : ℕ → E) (M : ℝ)
    (hM : SignedSumsBounded x M) (φ : E →L[ℝ] ℝ) :
    Summable (fun n => ‖φ (x n)‖) :=
  summable_of_sum_range_le (fun _ => norm_nonneg _)
    (sum_dual_norm_le_of_signed_sums_bounded x M hM φ)

/-- Bounded signed sums force the terms themselves to be weakly null. -/
theorem weaklyConverges_zero_of_signed_sums_bounded (x : ℕ → E) (M : ℝ)
    (hM : SignedSumsBounded x M) : WeaklyConverges ℝ E x 0 := by
  intro φ
  simpa only [map_zero] using
    (dual_summable_norm_of_signed_sums_bounded x M hM φ).of_norm.tendsto_atTop_zero

/-- Partial sums are weak Cauchy under the same signed-sum bound. -/
theorem weaklyCauchy_partialSums_of_signed_sums_bounded (x : ℕ → E) (M : ℝ)
    (hM : SignedSumsBounded x M) :
    WeaklyCauchy (𝕜 := ℝ) (fun N => ∑ n ∈ Finset.range N, x n) := by
  intro φ
  have h := (dual_summable_norm_of_signed_sums_bounded x M hM φ).of_norm.hasSum.tendsto_sum_nat
  simpa only [map_sum] using h.cauchySeq

/-- In a complete Schur space, every series with uniformly bounded signed partial sums converges. -/
theorem exists_tendsto_partialSums_of_signed_sums_bounded [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (x : ℕ → E) (M : ℝ) (hM : SignedSumsBounded x M) :
    ∃ a : E, Tendsto (fun N => ∑ n ∈ Finset.range N, x n) atTop (𝓝 a) :=
  exists_tendsto_of_weaklyCauchy hS (weaklyCauchy_partialSums_of_signed_sums_bounded x M hM)

/-- Uniformly bounded signed partial sums in a complete real Schur space
converge unconditionally, in Mathlib's full finite-subset sense. -/
theorem summable_of_signed_sums_bounded [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (x : ℕ → E) (M : ℝ) (hM : SignedSumsBounded x M) :
    Summable x :=
  summable_of_dual_summable hS x
    (fun φ => (dual_summable_norm_of_signed_sums_bounded x M hM φ).of_norm)

/-- A uniform bound on finite sign transformations converts bounded ordinary partial sums
into bounded signed partial sums. -/
theorem signedSumsBounded_of_sign_transform_bound (x : ℕ → E) (C M : ℝ) (hC : 0 ≤ C)
    (hpartial : ∀ N, ‖∑ n ∈ Finset.range N, x n‖ ≤ M)
    (htransform : ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, ε n = 1 ∨ ε n = -1) →
      ‖∑ n ∈ Finset.range N, ε n • x n‖ ≤ C * ‖∑ n ∈ Finset.range N, x n‖) :
    SignedSumsBounded x (C * M) := by
  intro N ε hε
  exact (htransform N ε hε).trans (mul_le_mul_of_nonneg_left (hpartial N) hC)

/-- The bounded-completeness argument for an unconditional expansion in a Schur space. -/
theorem bounded_completeness_of_sign_transform_bound [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (x : ℕ → E) (C M : ℝ) (hC : 0 ≤ C)
    (hpartial : ∀ N, ‖∑ n ∈ Finset.range N, x n‖ ≤ M)
    (htransform : ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, ε n = 1 ∨ ε n = -1) →
      ‖∑ n ∈ Finset.range N, ε n • x n‖ ≤ C * ‖∑ n ∈ Finset.range N, x n‖) :
    ∃ a : E, Tendsto (fun N => ∑ n ∈ Finset.range N, x n) atTop (𝓝 a) :=
  exists_tendsto_partialSums_of_signed_sums_bounded hS x (C * M)
    (signedSumsBounded_of_sign_transform_bound x C M hC hpartial htransform)

end RealScalar
end PL1.SchurBoundedCompleteness


