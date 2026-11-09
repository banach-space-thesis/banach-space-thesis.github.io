import LPCK.PrintedUpperTriangular
import ThesisCommon.Analysis.CompactForwardSelection

noncomputable section
open Filter
open scoped Topology

namespace LPCK.Printed
open ThesisCommon

variable {𝕜 E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {b : NormalizedSchauderBasis 𝕜 E} {hb : b.IsOneUnconditional}

open private norm_coordinate_comp_tendsto_zero from LPCK.PrintedUpperTriangular

/-- Lemma 3.1 for a normalised 1-unconditional basis. -/
theorem lemma_3_1_normalized (hcompact : ∀ S : X →L[𝕜] E, IsCompactOperator S)
    (T : X →L[𝕜] SchauderSum b hb X) :
    Tendsto (fun n => ‖(SchauderSum.coordinate n).comp T‖) atTop (𝓝 0) :=
  norm_coordinate_comp_tendsto_zero hcompact T

/-- Corollary 3.2, with the selected indices in a given infinite set. -/
theorem corollary_3_2_normalized (hcompact : ∀ S : X →L[𝕜] E, IsCompactOperator S)
    (T : X →L[𝕜] SchauderSum b hb X) {M : Set ℕ} (hM : M.Infinite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ (∀ k, e k ∈ M) ∧
      Summable (fun k => ‖(SchauderSum.coordinate (e k)).comp T‖) ∧
      (∑' k, ‖(SchauderSum.coordinate (e k)).comp T‖) < ε :=
  exists_increasing_summable_subsequence (fun _ => norm_nonneg _)
    (lemma_3_1_normalized hcompact T) hM hε

/-- Lemma 3.3 with any prescribed positive column bounds. -/
theorem lemma_3_3_normalized (hcompact : ∀ S : X →L[𝕜] E, IsCompactOperator S)
    (T : SchauderSum b hb X →L[𝕜] SchauderSum b hb X)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ k,
      Summable (fun j => ‖SchauderSum.block T (e (k + 1 + j)) (e k)‖) ∧
      (∑' j, ‖SchauderSum.block T (e (k + 1 + j)) (e k)‖) < δ k := by
  classical
  let col := fun n => T.comp (SchauderSum.singleL n)
  let Q (k n : ℕ) (B : Set ℕ) := ∃ g : ℕ ↪ ℕ, Set.range g = B ∧
    Summable (fun j => ‖SchauderSum.block T (g j) n‖) ∧
    (∑' j, ‖SchauderSum.block T (g j) n‖) < δ k
  have step (k : ℕ) (A : Set ℕ) (hA : A.Infinite) :
      ∃ n ∈ A, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ (∀ m ∈ B, n < m) ∧ Q k n B := by
    obtain ⟨n, hn⟩ := hA.nonempty
    obtain ⟨g, _, hmem, hsum, hsmall⟩ := corollary_3_2_normalized hcompact (col n)
      (infinite_above hA n) (hδ k)
    refine ⟨n, hn, Set.range g, Set.infinite_range_of_injective g.injective, ?_, ?_,
      g, rfl, ?_, ?_⟩
    · rintro m ⟨j, rfl⟩
      exact (hmem j).1
    · rintro m ⟨j, rfl⟩
      exact (hmem j).2
    · simpa only [SchauderSum.block, col, ContinuousLinearMap.comp_assoc] using hsum
    · simpa only [SchauderSum.block, col, ContinuousLinearMap.comp_assoc] using hsmall
  obtain ⟨f, _, _, _, _, _, _, hmono, hQ, htail⟩ := infinite_fusion Q Set.infinite_univ step
  let e : ℕ ↪ ℕ := ⟨f, hmono.injective⟩
  choose g hg hs hsmall using hQ
  refine ⟨e, hmono, fun k => ?_⟩
  have hsub : Set.range (coordinateTail e k) ⊆ Set.range (g k) := by
    rintro m ⟨j, rfl⟩
    rw [hg k]
    exact htail k (k + 1 + j) (by omega)
  obtain ⟨c, hc⟩ := exists_embedding_factor (g k) (coordinateTail e k) hsub
  have heq : (fun j => ‖SchauderSum.block T (e (k + 1 + j)) (e k)‖) =
      (fun j => ‖SchauderSum.block T (g k (c j)) (f k)‖) := by
    funext j
    rw [show g k (c j) = e (k + 1 + j) from congrArg (fun a : ℕ ↪ ℕ => a j) hc]
    rfl
  rw [heq]
  have hsum := (hs k).comp_injective c.injective
  refine ⟨hsum, ?_⟩
  exact (Summable.tsum_le_tsum_of_inj c c.injective
    (fun j _ => norm_nonneg (SchauderSum.block T (g k j) (f k))) (fun _ => le_rfl)
    hsum (hs k)).trans_lt (hsmall k)

end LPCK.Printed
