import Posets.WolfeLaminarNorming
import Posets.WolfeCZeroPreservation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Actual finite-span norming for a laminar family of compact clopen sets.
The exceptional set at each node contains all of its proper descendants. -/

noncomputable section
open Set Topology
namespace Posets

theorem wolfe_lower_bound_closedSpan {𝕜 ι E X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (v : ι → E) (T : E →L[𝕜] X) (c : ℝ)
    (h : ∀ (s : Finset ι) (a : ι → 𝕜),
      c * ‖∑ i ∈ s, a i • v i‖ ≤ ‖T (∑ i ∈ s, a i • v i)‖)
    {f : E} (hf : f ∈ (Submodule.span 𝕜 (Set.range v)).topologicalClosure) :
    c * ‖f‖ ≤ ‖T f‖ := by
  classical
  have hc : IsClosed {g : E | c * ‖g‖ ≤ ‖T g‖} :=
    isClosed_le (continuous_const.mul continuous_norm) T.continuous.norm
  apply closure_minimal (t := {g : E | c * ‖g‖ ≤ ‖T g‖}) ?_ hc hf
  intro g hg
  obtain ⟨a, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  exact h a.support a

theorem wolfe_laminar_sum_constant_cell {𝕜 K ι : Type*} [RCLike 𝕜]
    (A E : ι → Set K)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j))
    (hdesc : ∀ i j, A j ⊂ A i → A j ⊆ E i)
    (s : Finset ι) (a : ι → 𝕜) (x : K)
    (hx : (∑ j ∈ s, (A j).indicator (fun _ => a j) x) ≠ 0) :
    ∃ i ∈ s, x ∈ A i ∧ ∀ y ∈ A i \ E i,
      (∑ j ∈ s, (A j).indicator (fun _ => a j) y) =
        ∑ j ∈ s, (A j).indicator (fun _ => a j) x := by
  classical
  let t := s.filter (fun i => x ∈ A i)
  have ht : t.Nonempty := by
    by_contra h
    apply hx
    apply Finset.sum_eq_zero
    intro j hj
    have hxj : x ∉ A j := fun h' => h ⟨j, Finset.mem_filter.mpr ⟨hj, h'⟩⟩
    exact indicator_of_notMem hxj _
  obtain ⟨i, hi, hmin⟩ := t.exists_minimalFor A ht
  obtain ⟨his, hxi⟩ := Finset.mem_filter.mp hi
  refine ⟨i, his, hxi, ?_⟩
  intro y hy
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : A i ⊆ A j
  · rw [indicator_of_mem (hij hy.1), indicator_of_mem (hij hxi)]
  · by_cases hji : A j ⊆ A i
    · have hproper : A j ⊂ A i := ⟨hji, hij⟩
      have hyj : y ∉ A j := fun h => hy.2 (hdesc i j hproper h)
      have hxj : x ∉ A j := by
        intro h
        exact hij (hmin (Finset.mem_filter.mpr ⟨hj, h⟩) hji)
      rw [indicator_of_notMem hyj, indicator_of_notMem hxj]
    · have hd : Disjoint (A i) (A j) := (hlam i j).resolve_left hij |>.resolve_left hji
      rw [indicator_of_notMem (fun h => Set.disjoint_left.mp hd hy.1 h),
        indicator_of_notMem (fun h => Set.disjoint_left.mp hd hxi h)]

variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

local instance wolfeLaminarSpanDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeLaminarSpanDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfe_CZero_norm_attained [CompactSpace K] [Nonempty K]
    (f : JLMS.CZero 𝕜 K) : ∃ x, ‖f x‖ = ‖f‖ := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    f.continuous.norm.continuousOn
  refine ⟨x, le_antisymm (JLMS.norm_CZero_apply_le f x) ?_⟩
  apply (BoundedContinuousFunction.norm_le (norm_nonneg (f x))).mpr
  intro y
  exact hx (Set.mem_univ y)

/-- The row at a smallest cell containing a norming point controls every finite
linear combination of the indicators. This is the analytic norming step of
the clopen version of Wolfe's laminar-family argument. -/
theorem wolfe_laminar_sum_lower_bound [CompactSpace K] [Nonempty K]
    {ι X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : JLMS.AtomicDualModel 𝕜 K) (T : JLMS.CZero 𝕜 K →L[𝕜] X)
    (A E : ι → Set K) (μ : ι → WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (hA : ∀ i, IsClopen (A i)) (hcA : ∀ i, IsCompact (A i))
    (H : Set K) (hAH : ∀ i, A i ⊆ H)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j))
    (hdesc : ∀ i j, A j ⊂ A i → A j ⊆ E i)
    (hμ : ∀ i, μ i ∈ adjointUnitBall T) {ell η : ℝ}
    (hdiag : ∀ i, ell ≤ ‖μ i (JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i))‖)
    (houtside : ∀ i, wolfeMass M (μ i) (H \ A i) ≤ η)
    (hchildren : ∀ i, wolfeMass M (μ i) (E i) ≤ η)
    (s : Finset ι) (a : ι → 𝕜) :
    (ell - 3 * η) * ‖∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)‖ ≤
      ‖T (∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i))‖ := by
  classical
  let f : JLMS.CZero 𝕜 K := ∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)
  change (ell - 3 * η) * ‖f‖ ≤ ‖T f‖
  by_cases hf : f = 0
  · simp [hf]
  have heval (x : K) : f x = ∑ i ∈ s, (A i).indicator (fun _ => a i) x := by
    change JLMS.evaluation x f = _
    simp only [f, map_sum, map_smul, JLMS.evaluation_apply,
      JLMS.clopenIndicator_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hxi : x ∈ A i <;> simp [hxi]
  obtain ⟨x, hx⟩ := wolfe_CZero_norm_attained f
  have hfx : f x ≠ 0 := by
    intro h
    have : ‖f‖ = 0 := by simpa [h] using hx.symm
    exact hf (norm_eq_zero.mp this)
  obtain ⟨i, _, _, hi⟩ := wolfe_laminar_sum_constant_cell A E hlam hdesc s a x
    (by simpa only [← heval] using hfx)
  have hs : Function.support f ⊆ H := by
    intro y hy
    by_contra hyH
    apply hy
    rw [heval]
    apply Finset.sum_eq_zero
    intro j _
    exact indicator_of_notMem (fun h => hyH (hAH j h)) _
  have hc : ∀ y ∈ A i \ E i, f y = f x := by
    intro y hy
    simpa only [← heval] using hi y hy
  exact (wolfe_norming_of_small_exceptions M (μ i) f (hA i) (hcA i) (hAH i)
    hs (f x) hx hc (hdiag i) (houtside i) (hchildren i)).trans
      (norm_apply_le_of_mem_adjointUnitBall T (hμ i) f)

end Posets
