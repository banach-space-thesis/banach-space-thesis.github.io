import ThesisCommon.Analysis.L1BitingSelection
import ThesisCommon.Analysis.L1BitingAnnuli

/-! The disjoint form of biting selection for actual finite-measure L1.
All functions are genuine Lp classes, with exact decomposition and almost
everywhere disjointness rather than a postulated splitting witness. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
  [IsFiniteMeasure μ]

theorem exists_lOne_disjoint_biting_subsequence
    (f : ℕ → Lp 𝕜 1 μ) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ A : ℕ → Set X,
      ∃ hA : ∀ n, MeasurableSet (A n), Pairwise (Disjoint on A) ∧
      UniformIntegrable (fun n => (lpCut (A n)ᶜ (hA n).compl (f (r n)) : X → 𝕜)) 1 μ := by
  obtain ⟨r, hr, A, hA, hsum, hUI⟩ := exists_lOne_biting_subsequence f hf
  obtain ⟨s, hs, B, hB, hd, hsUI⟩ :=
    exists_disjoint_lOne_biting_annuli (f ∘ r) (fun n => hf _) A hA hsum hUI
  exact ⟨r ∘ s, hr.comp hs, B, hB, hd, hsUI⟩

theorem exists_lOne_uniformIntegrable_disjoint_splitting
    (f : ℕ → Lp 𝕜 1 μ) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ r : ℕ → ℕ, ∃ g h : ℕ → Lp 𝕜 1 μ, StrictMono r ∧
      (∀ n, f (r n) = g n + h n) ∧
      (∀ n, ∀ᵐ x ∂μ, g n x = 0 ∨ h n x = 0) ∧
      (Pairwise fun i j => ∀ᵐ x ∂μ, h i x = 0 ∨ h j x = 0) ∧
      UniformIntegrable (fun n => (g n : X → 𝕜)) 1 μ ∧
      (∀ n, ‖g n‖ ≤ ‖f (r n)‖) ∧ (∀ n, ‖h n‖ ≤ ‖f (r n)‖) := by
  obtain ⟨r, hr, A, hA, hd, hUI⟩ := exists_lOne_disjoint_biting_subsequence f hf
  let g : ℕ → Lp 𝕜 1 μ := fun n => lpCut (A n)ᶜ (hA n).compl (f (r n))
  let h : ℕ → Lp 𝕜 1 μ := fun n => lpCut (A n) (hA n) (f (r n))
  refine ⟨r, g, h, hr, ?_, ?_, ?_, hUI,
    fun n => norm_lpCut_le _ _ _, fun n => norm_lpCut_le _ _ _⟩
  · intro n
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (g n) (h n),
      lpCut_coe (A n)ᶜ (hA n).compl (f (r n)),
      lpCut_coe (A n) (hA n) (f (r n))] with x hs hg hh
    change g n x = _ at hg
    change h n x = _ at hh
    rw [hs, Pi.add_apply, hg, hh]
    by_cases hx : x ∈ A n <;> simp [hx]
  · intro n
    filter_upwards [lpCut_coe (A n)ᶜ (hA n).compl (f (r n)),
      lpCut_coe (A n) (hA n) (f (r n))] with x hg hh
    change g n x = _ at hg
    change h n x = _ at hh
    rw [hg, hh]
    by_cases hx : x ∈ A n <;> simp [hx]
  · intro i j hij
    filter_upwards [lpCut_coe (A i) (hA i) (f (r i)),
      lpCut_coe (A j) (hA j) (f (r j))] with x hi hj
    change h i x = _ at hi
    change h j x = _ at hj
    rw [hi, hj]
    by_cases hxi : x ∈ A i
    · have hxj : x ∉ A j := fun hxj => Set.disjoint_left.mp (hd hij) hxi hxj
      simp [hxj]
    · simp [hxi]

end ThesisCommon
