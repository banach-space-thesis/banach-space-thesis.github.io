import ThesisCommon.Analysis.SequenceCoordinates
import ThesisCommon.Analysis.InfiniteFusion
import Mathlib.Data.Fin.Embedding

/-! The ℓ₁ column estimates and infinite pigeonhole selection of PFP §3.2.
These are shared lemmas on the actual scalar lp space, over ℝ or ℂ. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Γ Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem ellOne_hasSum_norm (x : lp (fun _ : Γ => 𝕜) 1) :
    HasSum (fun i => ‖x i‖) ‖x‖ := by
  simpa using lp.hasSum_norm (by simp : 0 < (1 : ℝ≥0∞).toReal) x

theorem ellOne_norm_eq_tsum (x : lp (fun _ : Γ => 𝕜) 1) :
    ‖x‖ = ∑' i, ‖x i‖ := (ellOne_hasSum_norm x).tsum_eq.symm

/-- A column bound gives the operator bound by absolute summation. This is
Lemma 3.10, in the stronger form allowing any index set and any normed target. -/
theorem ellOne_norm_le_of_columns [DecidableEq Γ] (T : lp (fun _ : Γ => 𝕜) 1 →L[𝕜] Y)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T (lp.single 1 i (1 : 𝕜))‖ ≤ C) : ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro x
  have hsum := (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) x).map T T.continuous
  have hnorm := (ellOne_hasSum_norm x).mul_left C
  apply hsum.norm_le_of_bounded hnorm
  intro i
  change ‖T (lp.single 1 i (x i))‖ ≤ C * ‖x i‖
  have heq : (lp.single 1 i (x i) : lp (fun _ : Γ => 𝕜) 1) =
      x i • lp.single 1 i (1 : 𝕜) := by
    rw [← lp.single_smul]
    simp
  rw [heq, map_smul, norm_smul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hT i) (norm_nonneg _)

/-- Finite absolute column sums are bounded by the operator norm. -/
theorem ellOne_column_sum_le (T : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] lp (fun _ : ℕ => 𝕜) 1)
    (n : ℕ) (F : Finset ℕ) :
    ∑ m ∈ F, ‖T (lp.single 1 n (1 : 𝕜)) m‖ ≤ ‖T‖ := by
  have hsum := lp.sum_rpow_le_norm_rpow
    (by simp : 0 < (1 : ℝ≥0∞).toReal) (T (lp.single 1 n (1 : 𝕜))) F
  have hnorm := T.le_opNorm (lp.single 1 n (1 : 𝕜))
  have hs : ‖(lp.single 1 n (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) 1)‖ = 1 := by
    rw [lp.norm_single (by simp)]
    exact norm_one
  simp only [ENNReal.toReal_one, Real.rpow_one] at hsum
  simpa only [hs, mul_one] using hsum.trans hnorm

/-- The finite pigeonhole step in Lemma 3.9, inside any infinite retained set.
Uniformly bounded nonnegative column sums force a row small on an infinite tail. -/
theorem bounded_columns_small_row (w : ℕ → ℕ → ℝ) {M ε : ℝ}
    (hbound : ∀ n (F : Finset ℕ), ∑ m ∈ F, w m n ≤ M)
    (hε : 0 < ε) {A : Set ℕ} (hA : A.Infinite) :
    ∃ n ∈ A, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
      (∀ m ∈ B, n < m) ∧ ∀ m ∈ B, w n m < ε := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (M / ε)
  have hlarge : M < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  let a : Fin N ↪ ℕ := (Fin.valEmbedding.trans (hA.natEmbedding A)).trans
    (Function.Embedding.subtype A)
  let b := Finset.univ.sup (fun i : Fin N => a i)
  let L : Set ℕ := {m ∈ A | b < m}
  have hL : L.Infinite := infinite_above hA b
  let e : ℕ ↪ ℕ := (hL.natEmbedding L).trans (Function.Embedding.subtype L)
  have hs : ∀ m : ℕ, ∃ i : Fin N, w (a i) (e m) < ε := by
    intro m
    by_contra hn
    push_neg at hn
    have hlower : (N : ℝ) * ε ≤ ∑ i : Fin N, w (a i) (e m) := by
      calc
        _ = ∑ _i : Fin N, ε := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hn i)
    have hupper := hbound (e m) (Finset.univ.map a)
    rw [Finset.sum_map] at hupper
    exact (not_le_of_gt hlarge) (hlower.trans hupper)
  choose i hi using hs
  obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber i
  have hj' : (i ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
  refine ⟨a j, (hA.natEmbedding A j).property, e '' (i ⁻¹' {j}),
    (Set.infinite_image_iff e.injective.injOn).mpr hj', ?_, ?_, ?_⟩
  · rintro m ⟨r, _, rfl⟩
    exact (hL.natEmbedding L r).property.1
  · rintro m ⟨r, _, rfl⟩
    exact (Finset.le_sup (f := fun s : Fin N => a s) (Finset.mem_univ j)).trans_lt
      (hL.natEmbedding L r).property.2
  · rintro m ⟨r, hr, rfl⟩
    have heq : i r = j := hr
    simpa only [heq] using hi r

/-- Lemma 3.9 with a variable geometric error budget, as actually needed
in the proof of Theorem 3.11. Nested-set fusion preserves all earlier estimates. -/
theorem ellOne_future_interference
    (T : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] lp (fun _ : ℕ => 𝕜) 1)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i j, i < j →
      ‖T (lp.single 1 (f j) (1 : 𝕜)) (f i)‖ < δ i := by
  obtain ⟨f, hf, _, hsmall⟩ := infinite_fusion_entries
    (fun k n m => ‖T (lp.single 1 m (1 : 𝕜)) n‖ < δ k)
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
    (fun k A hA => bounded_columns_small_row
      (fun n m => ‖T (lp.single 1 m (1 : 𝕜)) n‖) (ellOne_column_sum_le T) (hδ k) hA)
  exact ⟨f, hf, hsmall⟩

end ThesisCommon
