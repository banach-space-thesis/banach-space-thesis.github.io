import ThesisCommon.Analysis.SchauderOperators
import ThesisCommon.Analysis.UnconditionalWeakNull

/-! Subsymmetric finite coefficient bounds and their actual canonical
subsequence operators. No isomorphism or factorisation conclusion is a
field of the definition. Constants need not be one. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon.NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (b : NormalizedSchauderBasis 𝕜 X)

def SubsymmetricWith (K C : ℝ) : Prop :=
  b.UnconditionalWith K ∧ 1 ≤ C ∧
    ∀ (f : ℕ → ℕ), StrictMono f → ∀ (F : Finset ℕ) (a : ℕ → 𝕜),
      ‖∑ n ∈ F, a n • b.vector (f n)‖ ≤ C * ‖∑ n ∈ F, a n • b.vector n‖ ∧
      ‖∑ n ∈ F, a n • b.vector n‖ ≤ C * ‖∑ n ∈ F, a n • b.vector (f n)‖

def IsSubsymmetric : Prop := ∃ K C : ℝ, b.SubsymmetricWith K C

theorem weakly_null_of_subsymmetric {K C : ℝ} (hs : b.SubsymmetricWith K C)
    (hnot : ¬ b.EquivalentEllOne) (φ : X →L[𝕜] 𝕜) :
    Tendsto (fun n => φ (b.vector n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  simp only [dist_zero_right]
  by_contra h
  push_neg at h
  have hfreq : ∃ᶠ n in atTop, ε ≤ ‖φ (b.vector n)‖ := Filter.frequently_atTop.mpr h
  obtain ⟨f, hf, hlarge⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨c, hc, hlower⟩ := b.subsequence_lower_of_large_functional hs.1 φ
    ⟨f, hf.injective⟩ hε hlarge
  have hC : 0 < C := zero_lt_one.trans_le hs.2.1
  apply hnot
  refine ⟨c / C, div_pos hc hC, ?_⟩
  intro F a
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hC).mpr
  exact (hlower F a).trans (by simpa only [mul_comm] using (hs.2.2 f hf F a).1)

theorem exists_subsymmetric_insertion [CompleteSpace X] {K C : ℝ}
    (hs : b.SubsymmetricWith K C) (f : ℕ → ℕ) (hf : StrictMono f) :
    ∃ B : X →L[𝕜] X, ‖B‖ ≤ C ∧ (∀ x, ‖x‖ ≤ C * ‖B x‖) ∧
      ∀ n, B (b.vector n) = b.vector (f n) := by
  obtain ⟨B, hB, hBe⟩ := b.exists_operator (fun n => b.vector (f n))
    (zero_le_one.trans hs.2.1) (fun F a => (hs.2.2 f hf F a).1)
  refine ⟨B, hB, ?_, hBe⟩
  intro x
  apply le_of_tendsto_of_tendsto' (b.expansion x).norm
    (((B.continuous.tendsto x).comp (b.expansion x)).norm.const_mul C)
  intro N
  simpa only [Function.comp_apply, map_sum, map_smul, hBe] using
    (hs.2.2 f hf (Finset.range N) (fun n => b.coord n x)).2

theorem exists_subsymmetric_compression [CompleteSpace X] {K C : ℝ}
    (hs : b.SubsymmetricWith K C) (f : ℕ → ℕ) (hf : StrictMono f) :
    ∃ A B : X →L[𝕜] X,
      A.comp B = ContinuousLinearMap.id 𝕜 X ∧ ‖A‖ ≤ C * K ∧ ‖B‖ ≤ C ∧
      (∀ n, B (b.vector n) = b.vector (f n)) ∧
      ∀ i x, b.coord i (A x) = b.coord (f i) x := by
  classical
  have hC : 0 ≤ C := zero_le_one.trans hs.2.1
  have hK : 0 ≤ K := zero_le_one.trans hs.1.1
  obtain ⟨B, hB, hBlower, hBe⟩ := b.exists_subsymmetric_insertion hs f hf
  let v : ℕ → X := fun n => if n ∈ Set.range f then
    b.vector (Function.invFun f n) else 0
  have hvin (n : ℕ) : v (f n) = b.vector n := by
    simp only [v, if_pos (Set.mem_range_self n)]
    rw [Function.leftInverse_invFun hf.injective n]
  have hBv (n : ℕ) : B (v n) = if n ∈ Set.range f then b.vector n else 0 := by
    by_cases hn : n ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hn
      rw [hvin, hBe, if_pos (Set.mem_range_self i)]
    · simp only [v, if_neg hn, map_zero]
  have hv (F : Finset ℕ) (a : ℕ → 𝕜) :
      ‖∑ n ∈ F, a n • v n‖ ≤ (C * K) * ‖∑ n ∈ F, a n • b.vector n‖ := by
    have hh := hs.1.2 F (fun n => if n ∈ Set.range f then a n else 0) a (by
      intro n _
      dsimp only
      split_ifs <;> simp)
    calc
      _ ≤ C * ‖B (∑ n ∈ F, a n • v n)‖ := hBlower _
      _ ≤ C * (K * ‖∑ n ∈ F, a n • b.vector n‖) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa only [map_sum, map_smul, hBv, ite_smul, zero_smul, smul_ite, smul_zero] using hh
      _ = _ := by ring
  obtain ⟨A, hA, hAe⟩ := b.exists_operator v (mul_nonneg hC hK) hv
  have hcoord (i : ℕ) : (b.coord i).comp A = b.coord (f i) := by
    apply b.operator_ext
    intro n
    simp only [ContinuousLinearMap.comp_apply, hAe]
    by_cases hn : n ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hn
      rw [hvin, b.biorthogonal, b.biorthogonal]
      simp only [hf.injective.eq_iff]
    · have hi : f i ≠ n := fun heq => hn ⟨i, heq⟩
      simp only [v, if_neg hn, map_zero, b.biorthogonal, if_neg hi]
  refine ⟨A, B, ?_, hA, hB, hBe, ?_⟩
  · apply b.operator_ext
    intro n
    simp only [ContinuousLinearMap.comp_apply, hBe, hAe, hvin, ContinuousLinearMap.id_apply]
  · intro i x
    exact DFunLike.congr_fun (hcoord i) x

end ThesisCommon.NormalizedSchauderBasis
