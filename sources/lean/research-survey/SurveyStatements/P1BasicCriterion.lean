import SurveyStatements.P1BasicSelection
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
From uniform initial-sum estimates to ordered basis expansions in the closed
span. Coordinate functionals are first bounded on the algebraic span and then
extended by Hahn--Banach.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Uniform initial-sum bounds also control every individual coefficient. -/
theorem uniform_partialSum_coefficient_bound {e : ℕ → X} {c : ℝ}
    (he : ∀ n, ‖e n‖ = 1) (hc : 0 < c)
    (hbound : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (a : ℕ → ℂ) {n M : ℕ} (hnM : n < M) :
    c * ‖a n‖ ≤ 2 * ‖sequencePartialSum e a M‖ := by
  have hdiff : a n • e n =
      sequencePartialSum e a (n + 1) - sequencePartialSum e a n := by
    simp [sequencePartialSum, Finset.sum_range_succ]
  have hnorm : ‖a n‖ ≤ ‖sequencePartialSum e a (n + 1)‖ +
      ‖sequencePartialSum e a n‖ := by
    calc
      ‖a n‖ = ‖a n • e n‖ := by simp [norm_smul, he]
      _ ≤ _ := by rw [hdiff]; exact norm_sub_le _ _
  have hnext := hbound (n + 1) M (Nat.succ_le_iff.mpr hnM) a
  have hprev := hbound n M hnM.le a
  nlinarith

/-- A supported finite sum agrees with any partial sum which includes its
support. -/
theorem linearCombination_eq_partialSum (e : ℕ → X) (a : ℕ →₀ ℂ)
    {M : ℕ} (hM : a.support ⊆ Finset.range M) :
    Finsupp.linearCombination ℂ e a = sequencePartialSum e a M := by
  exact Finsupp.linearCombination_apply_of_mem_supported ℂ (v := e) hM

theorem uniform_partialSum_finsupp_coefficient_bound {e : ℕ → X} {c : ℝ}
    (he : ∀ n, ‖e n‖ = 1) (hc : 0 < c)
    (hbound : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (a : ℕ →₀ ℂ) (n : ℕ) :
    c * ‖a n‖ ≤ 2 * ‖Finsupp.linearCombination ℂ e a‖ := by
  by_cases hn : n ∈ a.support
  · obtain ⟨M, hM⟩ := a.support.exists_nat_subset_range
    have hnM : n < M := Finset.mem_range.mp (hM hn)
    rw [linearCombination_eq_partialSum e a hM]
    exact uniform_partialSum_coefficient_bound he hc hbound a hnM
  · simp [Finsupp.notMem_support_iff.mp hn, norm_nonneg]

/-- The uniform initial-sum condition forces algebraic linear independence. -/
theorem uniform_partialSum_linearIndependent {e : ℕ → X} {c : ℝ}
    (he : ∀ n, ‖e n‖ = 1) (hc : 0 < c)
    (hbound : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖) :
    LinearIndependent ℂ e := by
  apply linearIndependent_iff.mpr
  intro a ha
  ext n
  have hb := uniform_partialSum_finsupp_coefficient_bound he hc hbound a n
  rw [ha, norm_zero, mul_zero] at hb
  have hn : ‖a n‖ = 0 := by nlinarith [norm_nonneg (a n)]
  simpa using norm_eq_zero.mp hn

/-- Uniformly bounded coefficients on the algebraic span extend to ambient
continuous linear coordinate functionals. -/
theorem uniform_partialSum_coordinate_functionals {e : ℕ → X} {c : ℝ}
    (he : ∀ n, ‖e n‖ = 1) (hc : 0 < c)
    (hbound : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖) :
    ∃ f : ℕ → X →L[ℂ] ℂ,
      ∀ n, ∀ x : Submodule.span ℂ (Set.range e),
        f n x = (uniform_partialSum_linearIndependent he hc hbound).repr x n := by
  let hli := uniform_partialSum_linearIndependent he hc hbound
  have hcoords : ∀ n : ℕ, ∃ f : X →L[ℂ] ℂ,
      ∀ x : Submodule.span ℂ (Set.range e), f x = hli.repr x n := by
    intro n
    let g : Submodule.span ℂ (Set.range e) →ₗ[ℂ] ℂ :=
      (Finsupp.lapply n).comp hli.repr
    have hg : ∀ x, ‖g x‖ ≤ (2 / c) * ‖x‖ := by
      intro x
      have hb := uniform_partialSum_finsupp_coefficient_bound he hc hbound (hli.repr x) n
      rw [hli.linearCombination_repr x] at hb
      change ‖hli.repr x n‖ ≤ (2 / c) * ‖(x : X)‖
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).mpr
      nlinarith
    let gC : Submodule.span ℂ (Set.range e) →L[ℂ] ℂ := g.mkContinuous (2 / c) hg
    obtain ⟨f, hf, _⟩ := exists_extension_norm_eq (Submodule.span ℂ (Set.range e)) gC
    exact ⟨f, hf⟩
  choose f hf using hcoords
  exact ⟨f, hf⟩

/-- The usual initial-sum criterion for a normalized basic sequence, with
ordered convergence throughout. Completeness of the ambient space is not
needed because expansion is asserted only for its existing closed span. -/
theorem basicSequence_of_uniform_partialSum {e : ℕ → X} {c : ℝ}
    (he : ∀ n, ‖e n‖ = 1) (hc : 0 < c)
    (hbound : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖) :
    IsBasicSequence e := by
  classical
  let hli := uniform_partialSum_linearIndependent he hc hbound
  obtain ⟨f, hf⟩ := uniform_partialSum_coordinate_functionals he hc hbound
  let P : ℕ → X → X := fun N x => sequencePartialSum e (fun n => f n x) N
  have hcontinuous (N : ℕ) : Continuous (P N) := by
    exact continuous_finset_sum _ fun n _ => (f n).continuous.smul continuous_const
  have hcoeff (n m : ℕ) : f n (e m) = if m = n then 1 else 0 := by
    let y : Submodule.span ℂ (Set.range e) := ⟨e m, Submodule.subset_span ⟨m, rfl⟩⟩
    have hr := hli.repr_eq_single m y rfl
    change f n y = _
    rw [hf n y, hr]
    simp [Finsupp.single_apply]
  have hspanbound (N : ℕ) (x : Submodule.span ℂ (Set.range e)) :
      c * ‖P N x‖ ≤ ‖(x : X)‖ := by
    obtain ⟨R, hR⟩ := (hli.repr x).support.exists_nat_subset_range
    let M := max N R
    have hM : (hli.repr x).support ⊆ Finset.range M :=
      hR.trans (Finset.range_mono (Nat.le_max_right N R))
    have hb := hbound N M (Nat.le_max_left N R) (hli.repr x)
    rw [← linearCombination_eq_partialSum e (hli.repr x) hM, hli.linearCombination_repr] at hb
    simpa only [P, hf] using hb
  have hclosedbound (N : ℕ) {x : X} (hx : x ∈ sequenceClosedSpan e) :
      c * ‖P N x‖ ≤ ‖x‖ := by
    have hclosed : IsClosed {x : X | c * ‖P N x‖ ≤ ‖x‖} :=
      isClosed_le (continuous_const.mul (hcontinuous N).norm) continuous_norm
    have hsub : (Submodule.span ℂ (Set.range e) : Set X) ⊆
        {x : X | c * ‖P N x‖ ≤ ‖x‖} := by
      intro x hx
      exact hspanbound N ⟨x, hx⟩
    exact closure_minimal hsub hclosed (by
      simpa only [sequenceClosedSpan, Submodule.topologicalClosure_coe] using hx)
  have hsub (N : ℕ) (x y : X) : P N (x - y) = P N x - P N y := by
    simp only [P, sequencePartialSum, map_sub, sub_smul, Finset.sum_sub_distrib]
  have hfinite (x : Submodule.span ℂ (Set.range e)) :
      ∃ R : ℕ, ∀ N ≥ R, P N x = (x : X) := by
    obtain ⟨R, hR⟩ := (hli.repr x).support.exists_nat_subset_range
    refine ⟨R, ?_⟩
    intro N hRN
    have hN := hR.trans (Finset.range_mono hRN)
    have hr := linearCombination_eq_partialSum e (hli.repr x) hN
    rw [hli.linearCombination_repr] at hr
    simpa only [P, hf] using hr.symm
  intro x hx
  refine ⟨fun n => f n x, ?_, ?_⟩
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    let δ := ε * c / (2 * (1 + c))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hxcl : x ∈ closure (Submodule.span ℂ (Set.range e) : Set X) := by
      simpa only [sequenceClosedSpan, Submodule.topologicalClosure_coe] using hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hxcl δ hδ
    obtain ⟨R, hR⟩ := hfinite ⟨y, hy⟩
    refine ⟨R, ?_⟩
    intro N hRN
    have hxy' : ‖x - y‖ < δ := by simpa [dist_eq_norm] using hxy
    have hxyspan : x - y ∈ sequenceClosedSpan e :=
      (sequenceClosedSpan e).sub_mem hx
        ((Submodule.span ℂ (Set.range e)).le_topologicalClosure hy)
    have hb := hclosedbound N hxyspan
    have hyN : P N y = y := hR N hRN
    have herr : ‖P N x - x‖ ≤ ‖P N (x - y)‖ + ‖x - y‖ := by
      calc
        ‖P N x - x‖ = ‖P N (x - y) - (x - y)‖ := by rw [hsub, hyN]; congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have hδeq : 2 * (1 + c) * δ = ε * c := by
      dsimp [δ]
      field_simp
    change dist (P N x) x < ε
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (P N (x - y)), norm_nonneg (x - y)]
  · intro a ha
    funext n
    have hfha := ((f n).continuous.tendsto x).comp ha
    have hevent : ∀ᶠ N : ℕ in atTop, f n (sequencePartialSum e a N) = a n := by
      filter_upwards [eventually_gt_atTop n] with N hN
      simp [sequencePartialSum, map_sum, map_smul, hcoeff, Finset.mem_range.mpr hN]
    have hconst : Tendsto (fun _ : ℕ => a n) atTop (𝓝 (f n x)) :=
      hfha.congr' hevent
    have hself : Tendsto (fun _ : ℕ => a n) atTop (𝓝 (a n)) := tendsto_const_nhds
    exact (tendsto_nhds_unique hconst hself).symm

end SurveyStatements.P1
