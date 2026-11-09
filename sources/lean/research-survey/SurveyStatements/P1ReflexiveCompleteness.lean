import SurveyStatements.P1BasicConstruction
import SurveyStatements.P4Gantmacher
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
Bounded completeness in the reflexive branch. The compactness input is the
proved Gantmacher/Banach--Alaoglu theorem, not an unfinished main theorem.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology Set
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Every bounded sequence in a reflexive normed space has a weak cluster
point. This asks for a cluster point, not a weakly convergent subsequence. -/
theorem reflexive_bounded_sequence_weakCluster
    (hRef : SurveyStatements.P4.IsReflexiveNormedSpace ℂ X)
    (s : ℕ → X) {B : ℝ} (hs : ∀ n, ‖s n‖ ≤ B) :
    ∃ x : X, MapClusterPt (toWeakSpace ℂ X x) atTop (fun n => toWeakSpace ℂ X (s n)) := by
  have hid := (SurveyStatements.P4.reflexive_iff_weaklyCompact_id).mp hRef
  obtain ⟨K, hK, hcover⟩ := (SurveyStatements.P4.weaklyCompact_iff_compact_cover
    (ContinuousLinearMap.id ℂ X)).mp hid
  let r : ℝ := B + 1
  have hB : 0 ≤ B := (norm_nonneg (s 0)).trans (hs 0)
  have hr : 0 < r := by dsimp [r]; linarith
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let L := (fun z : WeakSpace ℂ X => (r : ℂ) • z) '' K
  have hL : IsCompact L := hK.image (continuous_const.smul continuous_id)
  have hmember : ∀ n, toWeakSpace ℂ X (s n) ∈ L := by
    intro n
    have hunit : ‖(r : ℂ)⁻¹ • s n‖ ≤ 1 := by
      rw [norm_smul, norm_inv]
      have hnr : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
      rw [hnr, ← div_eq_inv_mul]
      apply (div_le_one hr).mpr
      exact (hs n).trans (by dsimp [r]; linarith)
    refine ⟨toWeakSpace ℂ X ((r : ℂ)⁻¹ • s n), hcover _ hunit, ?_⟩
    change toWeakSpace ℂ X ((r : ℂ) • ((r : ℂ)⁻¹ • s n)) = _
    simp [smul_smul, hr0]
  obtain ⟨z, _, hz⟩ := hL.exists_mapClusterPt
    (f := (atTop : Filter ℕ)) (u := fun n => toWeakSpace ℂ X (s n))
    (tendsto_principal.mpr (Eventually.of_forall hmember))
  exact ⟨(toWeakSpace ℂ X).symm z, by simpa using hz⟩

/-- A norm-closed complex linear subspace is closed in the actual weak
topology. -/
theorem isClosed_weak_closedSpan (e : ℕ → X) :
    IsClosed ((toWeakSpace ℂ X) '' (sequenceClosedSpan e : Set X)) := by
  letI : Module ℝ X := RestrictScalars.module ℝ ℂ X
  letI : IsScalarTower ℝ ℂ X := RestrictScalars.isScalarTower _ _ _
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars _ ℂ _
  letI : IsScalarTower ℝ ℂ (WeakSpace ℂ X) := inferInstanceAs (IsScalarTower ℝ ℂ X)
  have hconv : Convex ℝ (sequenceClosedSpan e : Set X) :=
    (sequenceClosedSpan e).restrictScalars ℝ |>.convex
  have hclosed : IsClosed (sequenceClosedSpan e : Set X) :=
    Submodule.isClosed_topologicalClosure _
  rw [← hclosed.closure_eq, hconv.toWeakSpace_closure ℂ]
  exact isClosed_closure

/-- Reflexivity makes a normalized sequence with uniform initial-sum bounds
boundedly complete. -/
theorem boundedlyComplete_of_reflexive_uniform_partialSum
    (hRef : SurveyStatements.P4.IsReflexiveNormedSpace ℂ X)
    {e : ℕ → X} {c : ℝ} (he : ∀ n, ‖e n‖ = 1) (hc : 0 < c)
    (hbound : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖) :
    IsBoundedlyComplete e := by
  classical
  have hbasic := basicSequence_of_uniform_partialSum he hc hbound
  refine ⟨hbasic, ?_⟩
  intro a ha
  obtain ⟨B, hB⟩ := ha
  obtain ⟨x, hx⟩ := reflexive_bounded_sequence_weakCluster hRef
    (sequencePartialSum e a) hB
  have hmember : ∀ N, sequencePartialSum e a N ∈ sequenceClosedSpan e := by
    intro N
    apply Submodule.sum_mem
    intro n hn
    exact Submodule.smul_mem _ _ ((Submodule.span ℂ (Set.range e)).le_topologicalClosure
      (Submodule.subset_span ⟨n, rfl⟩))
  have hxspan : x ∈ sequenceClosedSpan e := by
    let S := (toWeakSpace ℂ X) '' (sequenceClosedSpan e : Set X)
    have hm : Filter.map (fun N => toWeakSpace ℂ X (sequencePartialSum e a N)) atTop ≤ 𝓟 S := by
      apply tendsto_principal.mpr
      exact Eventually.of_forall fun N => ⟨_, hmember N, rfl⟩
    have hxcl := (hx.clusterPt.mono hm).mem_closure
    rw [(isClosed_weak_closedSpan e).closure_eq] at hxcl
    obtain ⟨y, hy, hxy⟩ := hxcl
    exact (toWeakSpace ℂ X).injective hxy ▸ hy
  obtain ⟨b, hb, _⟩ := hbasic x hxspan
  obtain ⟨f, hf⟩ := uniform_partialSum_coordinate_functionals he hc hbound
  let hli := uniform_partialSum_linearIndependent he hc hbound
  have hcoord (n m : ℕ) : f n (e m) = if m = n then 1 else 0 := by
    let y : Submodule.span ℂ (Set.range e) := ⟨e m, Submodule.subset_span ⟨m, rfl⟩⟩
    have hr := hli.repr_eq_single m y rfl
    change f n y = _
    rw [hf n y, hr]
    simp [Finsupp.single_apply]
  have hlimit (v : ℕ → ℂ) (n : ℕ) :
      Tendsto (fun N => f n (sequencePartialSum e v N)) atTop (𝓝 (v n)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with N hN
    simp [sequencePartialSum, map_sum, map_smul, hcoord, Finset.mem_range.mpr hN]
  have hax : ∀ n, f n x = a n := by
    intro n
    let g : WeakSpace ℂ X → ℂ := fun z => f n ((toWeakSpace ℂ X).symm z)
    have hcontinuous : Continuous g := WeakBilin.eval_continuous _ (f n)
    have hcluster := hx.continuousAt_comp hcontinuous.continuousAt
    have hcluster' : MapClusterPt (f n x) atTop
        (fun N => f n (sequencePartialSum e a N)) := hcluster
    exact eq_of_nhds_neBot (hcluster'.clusterPt.mono (hlimit a n))
  have hbx : ∀ n, f n x = b n := by
    intro n
    have h := ((f n).continuous.tendsto x).comp hb
    exact tendsto_nhds_unique h (hlimit b n)
  have hba : b = a := funext fun n => (hbx n).symm.trans (hax n)
  exact ⟨x, hba ▸ hb⟩

/-- The complete basic-sequence prerequisite for the reflexive branch. -/
theorem reflexive_exists_normalized_boundedlyComplete
    (hX : ¬ FiniteDimensional ℂ X)
    (hRef : SurveyStatements.P4.IsReflexiveNormedSpace ℂ X) :
    ∃ e : ℕ → X, (∀ n, ‖e n‖ = 1) ∧ IsBoundedlyComplete e := by
  obtain ⟨e, he, _, hb⟩ := exists_normalized_basicSequence_with_bound hX
    (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  exact ⟨e, he, boundedlyComplete_of_reflexive_uniform_partialSum hRef he (by norm_num) hb⟩

/-- Direct asymptotically monotone selection retains bounded completeness
in the reflexive case. -/
theorem reflexive_exists_asymptoticallyMonotone_boundedlyComplete
    (hX : ¬ FiniteDimensional ℂ X)
    (hRef : SurveyStatements.P4.IsReflexiveNormedSpace ℂ X) :
    ∃ e : ℕ → X, IsAsymptoticallyMonotone e ∧ IsBoundedlyComplete e ∧
      ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
        (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖ := by
  obtain ⟨e, he, hb⟩ := exists_asymptoticallyMonotone_with_bound hX
  exact ⟨e, he, boundedlyComplete_of_reflexive_uniform_partialSum hRef he.2.1
    (by norm_num) hb, hb⟩

end SurveyStatements.P1
