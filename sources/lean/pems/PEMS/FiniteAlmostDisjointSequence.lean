import PEMS.FiniteDisjointInputWitness
import PEMS.DisjointSignedBlockAssembly

/-! Source Lemma 5.4 on arbitrary finite measure spaces, over both fields.
The input sequence is genuinely normalized and disjoint, and its images are
approximated in norm by an actual disjoint sequence with the exact limiting
weak essential norm. No splitting, uniform-integrability, or block witness
is assumed. -/
noncomputable section
open MeasureTheory Set Filter Topology Function ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem lemma_5_4_real_finite
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : ¬IsWeaklyCompactOperator T) :
    ∃ (v : ℕ → LOne ℝ μ) (q : ℕ → LOne ℝ ν),
      (Pairwise fun i j => ∀ᵐ x ∂μ, v i x = 0 ∨ v j x = 0) ∧
      (Pairwise fun i j => ∀ᵐ y ∂ν, q i y = 0 ∨ q j y = 0) ∧
      (∀ n, ‖v n‖ = 1) ∧
      Tendsto (fun n => ‖T (v n) - q n‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖T (v n)‖) atTop (𝓝 (weakEssentialNorm T)) := by
  obtain ⟨u, A, hA, hu, hdu, hAd, hcut, hUI⟩ := exists_real_finite_disjointInput_extremal T hT
  let R : ℕ → LOne ℝ ν := fun n => lpCut (A n)ᶜ (hA n).compl (T (u n))
  obtain ⟨x, s, hs, hweak⟩ := exists_real_lOne_weak_subsequence_of_uniformIntegrable R hUI
  have heq (n : ℕ) : T (u n) - lpCut (A n) (hA n) (T (u n)) = R n := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (rclike_lOneCut_add_compl (A n) (hA n) (T (u n))).symm
  apply exists_normalized_disjoint_blocks_of_weak_residual T (u ∘ s)
    (fun n => lpCut (A (s n)) (hA _) (T (u (s n))))
    (fun i j hij => hdu (hs.injective.ne hij))
    (rclike_lOneCut_pairwise_ae_disjoint (A ∘ s) (fun n => hA _)
      (fun i j hij => hAd (hs.injective.ne hij)) (fun n => T (u (s n))))
    (fun n => hu _)
  · exact ⟨x, by simpa only [Function.comp_apply, heq] using hweak⟩
  · exact hcut.comp hs.tendsto_atTop

theorem lemma_5_4_complex_finite
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) (hT : ¬IsWeaklyCompactOperator T) :
    ∃ (v : ℕ → LOne ℂ μ) (q : ℕ → LOne ℂ ν),
      (Pairwise fun i j => ∀ᵐ x ∂μ, v i x = 0 ∨ v j x = 0) ∧
      (Pairwise fun i j => ∀ᵐ y ∂ν, q i y = 0 ∨ q j y = 0) ∧
      (∀ n, ‖v n‖ = 1) ∧
      Tendsto (fun n => ‖T (v n) - q n‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖T (v n)‖) atTop (𝓝 (weakEssentialNorm T)) := by
  obtain ⟨u, A, hA, hu, hdu, hAd, hcut, hUI⟩ := exists_complex_finite_disjointInput_extremal T hT
  let R : ℕ → LOne ℂ ν := fun n => lpCut (A n)ᶜ (hA n).compl (T (u n))
  obtain ⟨x, s, hs, hweak⟩ := exists_complex_lOne_weak_subsequence_of_uniformIntegrable R hUI
  have heq (n : ℕ) : T (u n) - lpCut (A n) (hA n) (T (u n)) = R n := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (rclike_lOneCut_add_compl (A n) (hA n) (T (u n))).symm
  apply exists_normalized_disjoint_blocks_of_weak_residual T (u ∘ s)
    (fun n => lpCut (A (s n)) (hA _) (T (u (s n))))
    (fun i j hij => hdu (hs.injective.ne hij))
    (rclike_lOneCut_pairwise_ae_disjoint (A ∘ s) (fun n => hA _)
      (fun i j hij => hAd (hs.injective.ne hij)) (fun n => T (u (s n))))
    (fun n => hu _)
  · exact ⟨x, by simpa only [Function.comp_apply, heq] using hweak⟩
  · exact hcut.comp hs.tendsto_atTop

end PEMS
