import ThesisCommon.Analysis.ContinuousMapComplexRiesz
import Mathlib.Topology.PartitionOfUnity

/-! Continuous complex functions on a compact Hausdorff space admit finite
positive partitions approximating them uniformly by sampled scalar values.
The coefficient bound is the original sup norm. -/
noncomputable section
open Set Finset
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem exists_continuousMap_complex_positive_partition
    (f : C(K, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset K, ∃ p : s → C(K, ℝ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      ‖(∑ i, f i.val • continuousMapOfReal (𝕜 := ℂ) (p i)) - f‖ ≤ ε := by
  classical
  let U : K → Set K := fun t => {x | ‖f x - f t‖ < ε}
  have hU (t : K) : IsOpen (U t) :=
    isOpen_lt (f.continuous.sub continuous_const).norm continuous_const
  have hcover : (univ : Set K) ⊆ ⋃ t, U t := by
    intro x hx
    exact mem_iUnion.mpr ⟨x, by simpa [U] using hε⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hcover' : (univ : Set K) ⊆ ⋃ i : s, U i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨p, hp⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : s => U i.val) (fun i => hU i.val) hcover'
  have hsum (x : K) : ∑ i : s, p i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one (mem_univ x)
  refine ⟨s, p, fun i x => p.nonneg i x, ?_, ?_⟩
  · ext x
    simpa using hsum x
  · apply (ContinuousMap.norm_le _ hε.le).mpr
    intro x
    have heq : ((∑ i : s, f i.val • continuousMapOfReal (𝕜 := ℂ) (p i)) - f) x =
        ∑ i : s, (f i.val - f x) * ((p i x : ℝ) : ℂ) := by
      have hsum' : ∑ i : s, ((p i x : ℝ) : ℂ) = 1 := by
        exact_mod_cast hsum x
      simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
        continuousMapOfReal_apply, smul_eq_mul]
      simp_rw [sub_mul]
      rw [sum_sub_distrib, ← mul_sum, hsum', mul_one]
      rfl
    rw [heq]
    calc
      ‖∑ i : s, (f i.val - f x) * ((p i x : ℝ) : ℂ)‖ ≤
          ∑ i : s, ‖(f i.val - f x) * ((p i x : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ i : s, ε * p i x := by
        apply sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (p.nonneg i x)]
        by_cases hz : p i x = 0
        · simp [hz]
        · have hx : x ∈ U i.val := hp i (subset_closure hz)
          have ht : ‖f i.val - f x‖ ≤ ε := by rw [norm_sub_rev]; exact hx.le
          exact mul_le_mul_of_nonneg_right ht (p.nonneg i x)
      _ = ε := by rw [← mul_sum, hsum, mul_one]

end ThesisCommon
