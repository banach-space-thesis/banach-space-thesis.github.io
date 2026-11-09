import SurveyStatements.P4Definitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sequential finite-rank approximation

This proves `p5:lem:strong-approximation` from the supplied paper. The
finite-rank maps are chosen on growing finite pieces of a dense sequence;
their common norm bound then extends convergence to every vector.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology

namespace SurveyStatements.P4

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Composing a finite-rank map on the right preserves finite rank. -/
theorem HasFiniteRank.comp_right
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {A : Y →L[𝕜] Z} (hA : HasFiniteRank 𝕜 A) (T : X →L[𝕜] Y) :
    HasFiniteRank 𝕜 (A.comp T) := by
  letI : FiniteDimensional 𝕜 (LinearMap.range A.toLinearMap) := hA
  apply Submodule.finiteDimensional_of_le
    (S₂ := LinearMap.range A.toLinearMap)
  rintro y ⟨x, rfl⟩
  exact ⟨T x, rfl⟩

theorem finiteRank_zero : HasFiniteRank 𝕜 (0 : E →L[𝕜] E) := by
  unfold HasFiniteRank
  change FiniteDimensional 𝕜 (LinearMap.range (0 : E →ₗ[𝕜] E))
  rw [LinearMap.range_zero]
  infer_instance

/-- The sum of two finite-rank maps is finite-rank. -/
theorem HasFiniteRank.add {A B : E →L[𝕜] E}
    (hA : HasFiniteRank 𝕜 A) (hB : HasFiniteRank 𝕜 B) : HasFiniteRank 𝕜 (A + B) := by
  letI : FiniteDimensional 𝕜 (LinearMap.range A.toLinearMap) := hA
  letI : FiniteDimensional 𝕜 (LinearMap.range B.toLinearMap) := hB
  apply Submodule.finiteDimensional_of_le
    (S₂ := LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap)
  rintro y ⟨x, rfl⟩
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

theorem HasFiniteRank.smul {A : E →L[𝕜] E} (hA : HasFiniteRank 𝕜 A) (a : 𝕜) :
    HasFiniteRank 𝕜 (a • A) := by
  letI : FiniteDimensional 𝕜 (LinearMap.range A.toLinearMap) := hA
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range A.toLinearMap)
  rintro y ⟨x, rfl⟩
  exact ⟨a • x, map_smul A a x⟩

theorem HasFiniteRank.sum {ι : Type*} (F : Finset ι) (A : ι → E →L[𝕜] E)
    (hA : ∀ n ∈ F, HasFiniteRank 𝕜 (A n)) : HasFiniteRank 𝕜 (∑ n ∈ F, A n) := by
  classical
  revert hA
  induction F using Finset.induction_on with
  | empty =>
      intro hA
      simpa using finiteRank_zero (𝕜 := 𝕜) (E := E)
  | @insert n F hn ih =>
      intro hA
      rw [Finset.sum_insert hn]
      exact (hA n (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi)))

/-- The sequential version of bounded approximation, with a common norm bound. -/
def HasSequentialBoundedApproximationProperty : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ → E →L[𝕜] E,
    (∀ n, HasFiniteRank 𝕜 (P n)) ∧ (∀ n, ‖P n‖ ≤ C) ∧
      ∀ x : E, Tendsto (fun n => P n x) atTop (𝓝 x)

/-- A common operator bound transfers pointwise convergence from a dense
sequence to the entire normed space. No completeness assumption is needed. -/
theorem strong_convergence_of_dense_sequence
    (d : ℕ → E) (hd : DenseRange d) (P : ℕ → E →L[𝕜] E)
    (C : ℝ) (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hdP : ∀ j, Tendsto (fun n => P n (d j)) atTop (𝓝 (d j))) :
    ∀ x : E, Tendsto (fun n => P n x) atTop (𝓝 x) := by
  intro x
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨j, hj⟩ := hd.exists_dist_lt x (div_pos hε (by positivity : 0 < 2 * (C + 1)))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hdP j) (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hsmall := hN n hn
  rw [dist_eq_norm] at hj hsmall ⊢
  have hbound : ‖P n (x - d j)‖ ≤ C * ‖x - d j‖ :=
    ((P n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hP n) (norm_nonneg _))
  have hdecomp : P n x - x = P n (x - d j) + (P n (d j) - d j) + (d j - x) := by
    rw [map_sub]
    abel
  have htri : ‖P n x - x‖ ≤ C * ‖x - d j‖ + ‖P n (d j) - d j‖ + ‖x - d j‖ := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add_right hbound _)) (by rw [norm_sub_rev]))
  have hj' : (C + 1) * ‖x - d j‖ < ε / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp hj
    nlinarith
  nlinarith

/-- BAP in a separable space yields uniformly bounded finite-rank maps
converging strongly to the identity (`p5:lem:strong-approximation`). -/
theorem HasBoundedApproximationProperty.sequential
    [TopologicalSpace.SeparableSpace E]
    (h : HasBoundedApproximationProperty 𝕜 E) :
    HasSequentialBoundedApproximationProperty (𝕜 := 𝕜) (E := E) := by
  classical
  obtain ⟨C, hC, h⟩ := h
  let d : ℕ → E := TopologicalSpace.denseSeq E
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq E
  have hchoose : ∀ n : ℕ, ∃ A : E →L[𝕜] E,
      HasFiniteRank 𝕜 A ∧ ‖A‖ ≤ C ∧
        ∀ j : ℕ, j ≤ n → ‖A (d j) - d j‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    let K : Set E := d '' (Finset.range (n + 1) : Set ℕ)
    have hK : IsCompact K := ((Finset.finite_toSet _).image d).isCompact
    obtain ⟨A, hA, hbound, happ⟩ := h K hK (1 / ((n : ℝ) + 1)) (by positivity)
    refine ⟨A, hA, hbound, ?_⟩
    intro j hj
    exact happ (d j) ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  choose P hfinite hnorm happ using hchoose
  refine ⟨C, hC, P, hfinite, hnorm, ?_⟩
  apply strong_convergence_of_dense_sequence d hd P C hC hnorm
  intro j
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp tendsto_one_div_add_atTop_nhds_zero_nat ε hε
  refine ⟨max N j, ?_⟩
  intro n hn
  have hNj := hN n (le_trans (le_max_left N j) hn)
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos] at hNj
  rw [dist_eq_norm]
  exact (happ n j (le_trans (le_max_right N j) hn)).trans hNj

/-- Uniform operator bounds make strong convergence uniform on each compact
set. This is the compact-set form of the sequential approximation property. -/
theorem uniformly_approximates_on_compact
    (P : ℕ → E →L[𝕜] E) (C : ℝ) (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hstrong : ∀ x : E, Tendsto (fun n => P n x) atTop (𝓝 x))
    (K : Set E) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ‖P n x - x‖ < ε := by
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨s, _, hs, hcover⟩ := hK.finite_cover_balls
    (div_pos hε (by positivity : 0 < 2 * (C + 1)))
  have hcenters : ∀ᶠ n in atTop, ∀ y ∈ s, ‖P n y - y‖ < ε / 2 := by
    apply hs.eventually_all.mpr
    intro y hy
    have he := Metric.tendsto_nhds.mp (hstrong y) (ε / 2) (by positivity)
    simpa only [dist_eq_norm] using he
  filter_upwards [hcenters] with n hn
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  rw [Metric.mem_ball, dist_eq_norm] at hxy
  have hbound : ‖P n (x - y)‖ ≤ C * ‖x - y‖ :=
    ((P n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hP n) (norm_nonneg _))
  have hdecomp : P n x - x = P n (x - y) + (P n y - y) + (y - x) := by
    rw [map_sub]
    abel
  have htri : ‖P n x - x‖ ≤ C * ‖x - y‖ + ‖P n y - y‖ + ‖x - y‖ := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add_right hbound _)) (by rw [norm_sub_rev]))
  have hxy' : (C + 1) * ‖x - y‖ < ε / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp hxy
    nlinarith
  have hy' := hn y hy
  nlinarith

theorem HasSequentialBoundedApproximationProperty.boundedApproximation
    (h : HasSequentialBoundedApproximationProperty (𝕜 := 𝕜) (E := E)) :
    HasBoundedApproximationProperty 𝕜 E := by
  obtain ⟨C, hC, P, hfinite, hnorm, hstrong⟩ := h
  refine ⟨C, hC, ?_⟩
  intro K hK ε hε
  obtain ⟨n, hn⟩ := (uniformly_approximates_on_compact P C hC hnorm hstrong K hK ε hε).exists
  exact ⟨P n, hfinite n, hnorm n, hn⟩

/-- In separable normed spaces, the two conventional formulations of BAP agree. -/
theorem boundedApproximation_iff_sequential [TopologicalSpace.SeparableSpace E] :
    HasBoundedApproximationProperty 𝕜 E ↔
      HasSequentialBoundedApproximationProperty (𝕜 := 𝕜) (E := E) :=
  ⟨HasBoundedApproximationProperty.sequential,
    HasSequentialBoundedApproximationProperty.boundedApproximation⟩

/-- The first approximation step for an operator into a separable BAP space:
finite-rank maps converge strongly to it, with a common operator norm bound. -/
theorem exists_bounded_finiteRank_strong_approximants
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [TopologicalSpace.SeparableSpace E]
    (hBAP : HasBoundedApproximationProperty 𝕜 E) (T : X →L[𝕜] E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ → X →L[𝕜] E,
      (∀ n, HasFiniteRank 𝕜 (A n)) ∧ (∀ n, ‖A n‖ ≤ C) ∧
        ∀ x : X, Tendsto (fun n => A n x) atTop (𝓝 (T x)) := by
  obtain ⟨C, hC, P, hfinite, hnorm, hstrong⟩ := hBAP.sequential
  refine ⟨C * ‖T‖, mul_nonneg hC (norm_nonneg _), fun n => (P n).comp T,
    fun n => (hfinite n).comp_right T, ?_, ?_⟩
  · intro n
    exact ((P n).opNorm_comp_le T).trans
      (mul_le_mul_of_nonneg_right (hnorm n) (norm_nonneg _))
  · intro x
    exact hstrong (T x)

end SurveyStatements.P4
