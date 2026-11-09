import SurveyStatements.P2SeparableRange
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-! Bounded columns synthesize an actual operator from scalar ell-one.
The absolutely convergent-series argument follows the dependency-free
recipe in ThesisCommon/Analysis/EllOneColumnOperators.lean. Only mathlib
and this project's proved separable-range core are imported. -/

noncomputable section
set_option autoImplicit false
open Filter Topology TopologicalSpace
open scoped BigOperators ENNReal

namespace SurveyStatements.P2

universe v
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem ellOne_synthesis_summable (x : ℕ → X) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) (a : lp (fun _ : ℕ => ℂ) 1) :
    Summable (fun n => a n • x n) := by
  have hn : Summable (fun n => ‖a n‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.memℓp a).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  apply (hn.mul_left C).of_norm_bounded
  intro n
  rw [norm_smul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hx n) (norm_nonneg _)

/-- A bounded sequence is the column sequence of this concrete synthesis map. -/
def ellOneSynthesis (x : ℕ → X) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ C) : lp (fun _ : ℕ => ℂ) 1 →L[ℂ] X :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' n, a n • x n
      map_add' := by
        intro a b
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (ellOne_synthesis_summable x C hx a).tsum_add
          (ellOne_synthesis_summable x C hx b)
      map_smul' := by
        intro z a
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
        exact (ellOne_synthesis_summable x C hx a).tsum_const_smul z }
    C (fun a => by
      have hn : HasSum (fun n => ‖a n‖) ‖a‖ := by
        simpa only [ENNReal.toReal_one, Real.rpow_one] using
          lp.hasSum_norm (p := 1) (by norm_num) a
      apply (ellOne_synthesis_summable x C hx a).hasSum.norm_le_of_bounded (hn.mul_left C)
      intro n
      rw [norm_smul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hx n) (norm_nonneg _))

theorem norm_ellOneSynthesis_le (x : ℕ → X) (C : ℝ) (hC hx) :
    ‖ellOneSynthesis x C hC hx‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

@[simp] theorem ellOneSynthesis_single (x : ℕ → X) (C : ℝ) (hC hx)
    (n : ℕ) (z : ℂ) :
    ellOneSynthesis x C hC hx (lp.single 1 n z) = z • x n := by
  change (∑' i, (lp.single (E := fun _ : ℕ => ℂ) 1 n z i) • x i) = z • x n
  rw [tsum_eq_single n]
  · simp
  · intro i hin
    simp [hin]

/-- All synthesized vectors lie in the separable closed span of the columns. -/
theorem ellOneSynthesis_range_isSeparable (x : ℕ → X) (C : ℝ) (hC hx) :
    IsSeparable (Set.range (ellOneSynthesis x C hC hx)) := by
  have hs : IsSeparable (closure (Submodule.span ℂ (Set.range x) : Set X)) :=
    (Set.countable_range x).isSeparable.span.closure
  apply hs.mono
  rintro y ⟨a, rfl⟩
  apply isClosed_closure.mem_of_tendsto
    (ellOne_synthesis_summable x C hx a).hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall fun N => subset_closure (by
    apply Submodule.sum_mem
    intro n hn
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩))

theorem ellOne_unitVectors_dist_lower {m n : ℕ} (hmn : m ≠ n) :
    (1 : ℝ) ≤ dist
      (lp.single (E := fun _ : ℕ => ℂ) 1 m 1) (lp.single 1 n 1) := by
  have h := lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (lp.single (E := fun _ : ℕ => ℂ) 1 m 1 - lp.single 1 n 1) m
  simpa [dist_eq_norm, hmn] using h

/-- No strict subsequence of the actual ell-one unit vectors converges. -/
theorem ellOne_unitVectors_not_tendsto (ν : ℕ → ℕ) (hν : StrictMono ν)
    (a : lp (fun _ : ℕ => ℂ) 1) :
    ¬ Tendsto (fun n => lp.single (E := fun _ : ℕ => ℂ) 1 (ν n) 1) atTop (𝓝 a) := by
  intro hlim
  have hc := Metric.cauchySeq_iff.mp hlim.cauchySeq
  obtain ⟨N, hN⟩ := hc (1 / 2) (by norm_num)
  have hdist := hN N (le_refl N) (N + 1) (by omega)
  have hne : ν N ≠ ν (N + 1) := (hν (by omega)).ne
  have hlower := ellOne_unitVectors_dist_lower hne
  linarith

/-- An actual ell-one coefficient map with bounded unit-vector lifts gives a
noncompact operator with separable range. -/
theorem ellOne_lifts_separable_noncompact
    (Θ : X →L[ℂ] lp (fun _ : ℕ => ℂ) 1) (x : ℕ → X)
    (C : ℝ) (hC : 0 ≤ C) (hx : ∀ n, ‖x n‖ ≤ C)
    (hΘ : ∀ n, Θ (x n) = lp.single 1 n 1) :
    IsSeparable (Set.range ((ellOneSynthesis x C hC hx).comp Θ)) ∧
      ¬ IsCompactOperator ((ellOneSynthesis x C hC hx).comp Θ) := by
  constructor
  · exact isSeparableRange_comp_right (ellOneSynthesis_range_isSeparable x C hC hx) Θ
  · intro hcompact
    let T := (ellOneSynthesis x C hC hx).comp Θ
    have hTx : ∀ n, T (x n) = x n := by
      intro n
      simp [T, hΘ n]
    have hK := hcompact.isCompact_closure_image_closedBall C
    have hmem : ∀ n, T (x n) ∈ closure (T '' Metric.closedBall 0 C) := by
      intro n
      apply subset_closure
      exact ⟨x n, by simpa [Metric.mem_closedBall, dist_zero_right] using hx n, rfl⟩
    obtain ⟨y, _, ν, hν, hlim⟩ := hK.tendsto_subseq hmem
    have htheta := Θ.continuous.tendsto y |>.comp hlim
    change Tendsto (fun n => Θ (T (x (ν n)))) atTop (𝓝 (Θ y)) at htheta
    have hunit : Tendsto (fun n => lp.single (E := fun _ : ℕ => ℂ) 1 (ν n) 1)
        atTop (𝓝 (Θ y)) := by
      simpa only [hTx, hΘ] using htheta
    exact ellOne_unitVectors_not_tendsto ν hν (Θ y) hunit

theorem exists_separable_noncompact_of_ellOne_unit_lifts
    (Θ : X →L[ℂ] lp (fun _ : ℕ => ℂ) 1) (x : ℕ → X)
    (C : ℝ) (hC : 0 ≤ C) (hx : ∀ n, ‖x n‖ ≤ C)
    (hΘ : ∀ n, Θ (x n) = lp.single 1 n 1) :
    ∃ T : BoundedOperators X, IsSeparable (Set.range T) ∧ ¬ IsCompactOperator T :=
  ⟨(ellOneSynthesis x C hC hx).comp Θ,
    ellOne_lifts_separable_noncompact Θ x C hC hx hΘ⟩

end SurveyStatements.P2
