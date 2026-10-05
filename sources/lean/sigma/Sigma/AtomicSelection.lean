import Sigma.ProofTargets
import JLMS.L1Restriction
import ThesisCommon.Analysis.OffDiagonalSum

/-! Atomic fibre estimates used in Lemma 4.7. -/
noncomputable section
open Set
namespace SigmaNonprimarity

def fibreWeight (μ : lp (fun _ : Point => ℝ) 1) (n : ℕ) : ℝ :=
  |μ (n, false)| + |μ (n, true)|

theorem fibreWeight_nonneg (μ : lp (fun _ : Point => ℝ) 1) (n : ℕ) :
    0 ≤ fibreWeight μ n := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem fibreWeight_summable (μ : lp (fun _ : Point => ℝ) 1) :
    Summable (fibreWeight μ) := by
  simpa only [fibreWeight, tsum_bool, Real.norm_eq_abs] using
    (JLMS.ellOneOn_summable_norm μ).prod

theorem tsum_fibreWeight (μ : lp (fun _ : Point => ℝ) 1) :
    ∑' n, fibreWeight μ n = ‖μ‖ := by
  rw [JLMS.ellOneOn_norm_eq_tsum, (JLMS.ellOneOn_summable_norm μ).tsum_prod]
  simp only [tsum_bool, Real.norm_eq_abs, fibreWeight]

theorem fibreWeight_sum_le_norm (μ : lp (fun _ : Point => ℝ) 1) (F : Finset ℕ) :
    ∑ n ∈ F, fibreWeight μ n ≤ ‖μ‖ := by
  rw [← tsum_fibreWeight]
  exact (fibreWeight_summable μ).sum_le_tsum F (fun n _ => fibreWeight_nonneg μ n)

theorem abs_coordinate_le_norm (μ : lp (fun _ : Point => ℝ) 1) (n : ℕ) :
    |μ (n, false)| ≤ ‖μ‖ := by
  have h := fibreWeight_sum_le_norm μ {n}
  simp only [Finset.sum_singleton, fibreWeight] at h
  exact (le_add_of_nonneg_right (abs_nonneg _)).trans h

def graphSplitter (J : Set ℕ) (σ : ℕ → Bool) : Set Point :=
  {p | p.1 ∈ J ∧ p.2 = σ p.1}

theorem graphSplitter_splits (J : Set ℕ) (σ : ℕ → Bool) : Splits J (graphSplitter J σ) := by
  refine ⟨fun p hp => hp.1, ?_⟩
  intro n hn
  cases hσ : σ n <;> simp [graphSplitter, hn, hσ]

theorem graphSplitter_complement (J : Set ℕ) (σ : ℕ → Bool) :
    cylinder J \ graphSplitter J σ = graphSplitter J (fun n => !(σ n)) := by
  ext ⟨n, i⟩
  cases i <;> cases hσ : σ n <;> simp [cylinder, graphSplitter, hσ]

theorem atomic_summable (μ : lp (fun _ : Point => ℝ) 1) : Summable (fun p => μ p) :=
  (JLMS.ellOneOn_summable_norm μ).of_norm

theorem mass_graphSplitter (μ : lp (fun _ : Point => ℝ) 1) (J : Set ℕ) (σ : ℕ → Bool) :
    mass μ (graphSplitter J σ) = ∑' n, J.indicator (fun k => μ (k, σ k)) n := by
  classical
  rw [mass, tsum_subtype, ((atomic_summable μ).indicator (graphSplitter J σ)).tsum_prod]
  apply tsum_congr
  intro n
  rw [tsum_bool]
  by_cases hn : n ∈ J <;> cases hσ : σ n <;>
    simp [Set.indicator_apply, graphSplitter, hn, hσ]

def splitterRow (μ : lp (fun _ : Point => ℝ) 1) (J : Set ℕ) (σ : ℕ → Bool) : ℕ → ℝ :=
  J.indicator (fun n => μ (n, σ n) - μ (n, !(σ n)))

theorem mass_splitter_difference (μ : lp (fun _ : Point => ℝ) 1)
    (J : Set ℕ) (σ : ℕ → Bool) :
    mass μ (graphSplitter J σ) - mass μ (cylinder J \ graphSplitter J σ) =
      ∑' n, splitterRow μ J σ n := by
  rw [graphSplitter_complement, mass_graphSplitter, mass_graphSplitter]
  have hs (τ : ℕ → Bool) : Summable (fun n => μ (n, τ n)) :=
    (atomic_summable μ).comp_injective (fun _ _ h => congrArg Prod.fst h)
  rw [← ((hs σ).indicator J).tsum_sub ((hs (fun n => !(σ n))).indicator J)]
  apply tsum_congr
  intro n
  simp only [splitterRow, Set.indicator_sub]

theorem splitterRow_abs_le (μ : lp (fun _ : Point => ℝ) 1)
    (J : Set ℕ) (σ : ℕ → Bool) (n : ℕ) :
    |splitterRow μ J σ n| ≤ fibreWeight μ n := by
  classical
  by_cases hn : n ∈ J
  · simp only [splitterRow, Set.indicator_of_mem hn]
    cases hσ : σ n
    · simpa [hσ, fibreWeight] using abs_sub (μ (n, false)) (μ (n, true))
    · simpa [hσ, fibreWeight, add_comm] using abs_sub (μ (n, true)) (μ (n, false))
  · simp [splitterRow, Set.indicator_of_notMem hn, fibreWeight_nonneg]

theorem mass_splitter_offdiagonal (μ : lp (fun _ : Point => ℝ) 1)
    (J J₀ : Set ℕ) (hJ : J ⊆ J₀) (σ : ℕ → Bool) (n : ℕ) :
    |mass μ (graphSplitter J σ) - mass μ (cylinder J \ graphSplitter J σ) -
      splitterRow μ J σ n| ≤ ∑' k : ↥(J₀ \ {n}), fibreWeight μ k.val := by
  rw [mass_splitter_difference]
  apply ThesisCommon.abs_tsum_sub_le_offdiagonal _ _ (fibreWeight_summable μ)
    (splitterRow_abs_le μ J σ) J₀
  exact Set.support_indicator_subset.trans hJ

theorem atomic_rosenthal_selection (μ : ℕ → lp (fun _ : Point => ℝ) 1)
    (hμ : ∀ n, ‖μ n‖ ≤ 1) (C : Set ℕ) (hC : C.Infinite) (δ : ℝ) (hδ : 0 < δ) :
    ∃ J₀ : Set ℕ, J₀ ⊆ C ∧ J₀.Infinite ∧
      ∀ n ∈ J₀, (∑' k : ↥(J₀ \ {n}), fibreWeight (μ n) k.val) < δ := by
  exact ThesisCommon.rosenthal_selection (fun n => fibreWeight (μ n))
    (fun n => fibreWeight_nonneg (μ n))
    (fun n F => (fibreWeight_sum_le_norm (μ n) F).trans (hμ n)) C hC δ hδ

end SigmaNonprimarity
