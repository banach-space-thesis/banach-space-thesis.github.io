import PEMS.WeaklyConvergentSignedBlocks
import PEMS.MeasureDefinitions
import ThesisCommon.Analysis.L1DisjointBlocks
import ThesisCommon.Analysis.AlmostDisjointNormalization

/-! The signed-block step in source Lemma 5.4. Genuine weak convergence
of the residual produces normalized disjoint input blocks and disjoint
output blocks. Their small norm error and limiting norm are proved from
the exact finite disjoint-sum identities. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped BigOperators Topology
namespace PEMS
variable {𝕜 X Y : Type*} [RCLike 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_normalized_disjoint_blocks_of_weak_residual
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (u : ℕ → LOne 𝕜 μ) (p : ℕ → LOne 𝕜 ν)
    (hdu : Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0)
    (hdp : Pairwise fun i j => ∀ᵐ y ∂ν, p i y = 0 ∨ p j y = 0)
    (hu : ∀ n, ‖u n‖ = 1)
    (hweak : ∃ l : LOne 𝕜 ν,
      Tendsto (fun n => toWeakSpace 𝕜 (LOne 𝕜 ν) (T (u n) - p n)) atTop
        (𝓝 (toWeakSpace 𝕜 (LOne 𝕜 ν) l)))
    {c : ℝ} (hp : Tendsto (fun n => ‖p n‖) atTop (𝓝 c)) :
    ∃ (v : ℕ → LOne 𝕜 μ) (q : ℕ → LOne 𝕜 ν),
      (Pairwise fun i j => ∀ᵐ x ∂μ, v i x = 0 ∨ v j x = 0) ∧
      (Pairwise fun i j => ∀ᵐ y ∂ν, q i y = 0 ∨ q j y = 0) ∧
      (∀ n, ‖v n‖ = 1) ∧
      Tendsto (fun n => ‖T (v n) - q n‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖T (v n)‖) atTop (𝓝 c) := by
  classical
  obtain ⟨i, α, hi, hα, hlim⟩ := proposition_5_2 hweak
  let s : ℕ → Finset ℕ := fun n => Finset.Ioc (i n) (i (n + 1))
  let v : ℕ → LOne 𝕜 μ := fun n => ∑ j ∈ s n, α j • u j
  let q : ℕ → LOne 𝕜 ν := fun n => ∑ j ∈ s n, α j • p j
  have hs : Pairwise fun n m => Disjoint (s n) (s m) :=
    pairwise_disjoint_successive_Ioc hi
  have hv : ∀ n, ‖v n‖ = 1 := by
    intro n
    change ‖∑ j ∈ s n, α j • u j‖ = 1
    rw [norm_lOne_finset_smul_sum_of_ae_disjoint u hdu]
    simpa only [hu, mul_one] using hα n
  have herr : Tendsto (fun n => ‖T (v n) - q n‖) atTop (𝓝 0) := by
    have heq (n : ℕ) : T (v n) - q n =
        ∑ j ∈ s n, α j • (T (u j) - p j) := by
      simp only [v, q, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    simpa only [heq, s, norm_zero] using hlim.norm
  have hq : Tendsto (fun n => ‖q n‖) atTop (𝓝 c) := by
    have h := tendsto_weighted_successive_blocks hp i hi (fun j => ‖α j‖)
      (fun j => norm_nonneg _) hα
    simpa only [q, s, norm_lOne_finset_smul_sum_of_ae_disjoint p hdp] using h
  refine ⟨v, q, ae_disjoint_lOne_block_sums u hdu α s hs,
    ae_disjoint_lOne_block_sums p hdp α s hs, hv, herr, ?_⟩
  apply tendsto_norm_model_of_norm_error (f := q) (g := fun n => T (v n)) _ hq
  simpa only [norm_sub_rev] using herr

end PEMS
