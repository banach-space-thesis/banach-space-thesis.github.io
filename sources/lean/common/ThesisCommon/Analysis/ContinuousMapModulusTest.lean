import ThesisCommon.Analysis.ContinuousMapComplexModulus

/-! Sharp test functions for the real and complex dual moduli of C(K).
Finite signs or phases of positive decompositions retain pointwise bounds. -/
noncomputable section
open Set Finset
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon

theorem exists_dualModulus_test
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
    (φ : E →L[ℝ] ℝ) {x : E} (hx : 0 ≤ x) {r : ℝ}
    (hr : r < dualModulus φ x) :
    ∃ y : E, |y| ≤ x ∧ r < φ y := by
  classical
  rw [dualModulus_apply_of_nonneg φ x hx] at hr
  have hex : ∃ d : PositiveDecomposition x, r < d.value φ := by
    by_contra! hn
    apply (not_le_of_gt hr)
    apply (dualModulusPos_isLUB φ x hx).2
    rintro _ ⟨d, rfl⟩
    exact hn d
  obtain ⟨d, hd⟩ := hex
  let y : d.Index → E := fun i => if 0 ≤ φ (d.part i) then d.part i else -d.part i
  have hy (i : d.Index) : |y i| = d.part i := by
    dsimp [y]
    split <;> simp only [abs_neg, abs_of_nonneg (d.nonneg i)]
  refine ⟨∑ i, y i, ?_, ?_⟩
  · calc
      |∑ i, y i| ≤ ∑ i, |y i| := lattice_abs_sum_le _ _
      _ = x := by simp_rw [hy]; exact d.sum_eq
  · have he : φ (∑ i, y i) = d.value φ := by
      rw [map_sum]
      apply sum_congr rfl
      intro i _
      dsimp [y]
      split_ifs with h
      · exact (abs_of_nonneg h).symm
      · rw [map_neg, abs_of_neg (lt_of_not_ge h)]
    rwa [he]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem exists_continuousMap_complex_modulus_test (φ : C(K, ℂ) →L[ℂ] ℂ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) {r : ℝ}
    (hr : r < continuousMapComplexModulus φ f) :
    ∃ g : C(K, ℂ), (∀ t, ‖g t‖ ≤ f t) ∧ r < ‖φ g‖ := by
  classical
  rw [continuousMapComplexModulus_apply_nonneg φ f hf] at hr
  have hex : ∃ d : PositiveDecomposition f,
      r < continuousMapComplexDecompositionValue φ d := by
    by_contra! hn
    apply (not_le_of_gt hr)
    apply (continuousMapComplexModulusPos_isLUB φ f hf).2
    rintro _ ⟨d, rfl⟩
    exact hn d
  obtain ⟨d, hd⟩ := hex
  choose c hc he using fun i : d.Index =>
    Complex.exists_norm_eq_mul_self (φ (continuousMapOfReal (d.part i)))
  let g : C(K, ℂ) := ∑ i, c i • continuousMapOfReal (d.part i)
  refine ⟨g, ?_, ?_⟩
  · intro t
    calc
      ‖g t‖ = ‖∑ i, c i * ((d.part i t : ℝ) : ℂ)‖ := by simp [g, smul_eq_mul]
      _ ≤ ∑ i, ‖c i * ((d.part i t : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ = ∑ i, d.part i t := by
        apply sum_congr rfl
        intro i _
        rw [norm_mul, hc, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (d.nonneg i t)]
      _ = f t := by simpa using congrArg (fun h : C(K, ℝ) => h t) d.sum_eq
  · have heval : continuousMapComplexDecompositionValue φ d = (φ g).re := by
      simp only [continuousMapComplexDecompositionValue, g, map_sum, map_smul,
        Complex.re_sum, smul_eq_mul]
      apply sum_congr rfl
      intro i _
      rw [← he i]
      rfl
    exact (hd.trans_eq heval).trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm _))

end ThesisCommon
