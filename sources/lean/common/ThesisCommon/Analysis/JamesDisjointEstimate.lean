import ThesisCommon.Analysis.JamesSequenceLpEmbedding
import Mathlib.Analysis.MeanInequalities

/-! A finite family of James vectors with pairwise disjoint coordinate
supports satisfies an upper lp estimate. Each edge of a path meets at most
two supports, so the estimate follows from the scalar two-term power bound.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}

theorem norm_sum_rpow_le_two_of_sparse (F : Finset ι) (v : ι → 𝕜) {q : ℝ}
    (hq : 1 ≤ q)
    (hcard : (F.filter (fun i => v i ≠ 0)).card ≤ 2) :
    ‖∑ i ∈ F, v i‖ ^ q ≤ 2 ^ (q - 1) * ∑ i ∈ F, ‖v i‖ ^ q := by
  classical
  let S := F.filter (fun i => v i ≠ 0)
  have hsum : ∑ i ∈ S, v i = ∑ i ∈ F, v i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    by_contra hv
    exact hn (Finset.mem_filter.mpr ⟨hi, hv⟩)
  rw [← hsum]
  calc
    ‖∑ i ∈ S, v i‖ ^ q ≤ (∑ i ∈ S, ‖v i‖) ^ q :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_sum_le _ _) (by linarith)
    _ ≤ (S.card : ℝ) ^ (q - 1) * ∑ i ∈ S, ‖v i‖ ^ q :=
      Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S (f := fun i => ‖v i‖) hq
        (fun _ _ => norm_nonneg _)
    _ ≤ 2 ^ (q - 1) * ∑ i ∈ F, ‖v i‖ ^ q := by
      apply mul_le_mul
      · apply Real.rpow_le_rpow (Nat.cast_nonneg _)
          (show (S.card : ℝ) ≤ 2 by exact_mod_cast hcard) (by linarith)
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Real.rpow_nonneg (norm_nonneg _) _)
      · exact Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
      · positivity

variable (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem james_disjoint_path_rpow_le (F : Finset ι) (x : ι → JamesSequenceSpace 𝕜 p)
    (hdisj : ∀ n : ℕ, (F.filter (fun i => x i n ≠ 0)).card ≤ 1) (s : JamesPath) :
    ‖jamesPathMap 𝕜 p s (∑ i ∈ F, x i).val‖ ^ p.val.toReal ≤
      2 ^ (p.val.toReal - 1) * ∑ i ∈ F, ‖x i‖ ^ p.val.toReal := by
  classical
  have hq : 1 ≤ p.val.toReal := by
    exact_mod_cast (ENNReal.toReal_le_toReal (by simp) hp).mpr p.property
  have heq : jamesPathMap 𝕜 p s (∑ i ∈ F, x i).val =
      ∑ i ∈ F, jamesPathMap 𝕜 p s (x i).val := by
    change ((jamesPathMap 𝕜 p s).comp (JamesSequenceSpace.toCZero (𝕜 := 𝕜) (p := p)))
      (∑ i ∈ F, x i) = _
    simp only [map_sum, ContinuousLinearMap.comp_apply]
    rfl
  rw [heq, finitePiLp_norm_rpow p hp]
  calc
    ∑ j, ‖(∑ i ∈ F, jamesPathMap 𝕜 p s (x i).val) j‖ ^ p.val.toReal ≤
        ∑ j : Fin s.length, 2 ^ (p.val.toReal - 1) *
          ∑ i ∈ F, ‖jamesPathMap 𝕜 p s (x i).val j‖ ^ p.val.toReal := by
      apply Finset.sum_le_sum
      intro j _
      have hcard : (F.filter (fun i => jamesPathMap 𝕜 p s (x i).val j ≠ 0)).card ≤ 2 := by
        have hsub : F.filter (fun i => jamesPathMap 𝕜 p s (x i).val j ≠ 0) ⊆
            (F.filter (fun i => x i (s.index j.castSucc) ≠ 0)) ∪
              (F.filter (fun i => x i (s.index j.succ) ≠ 0)) := by
          intro i hi
          obtain ⟨hiF, hiv⟩ := Finset.mem_filter.mp hi
          by_cases hl : x i (s.index j.castSucc) = 0
          · apply Finset.mem_union_right
            apply Finset.mem_filter.mpr
            refine ⟨hiF, ?_⟩
            intro hr
            apply hiv
            simp [jamesPathMap_apply, hl, hr]
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiF, hl⟩)
        exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
          (by have hl := hdisj (s.index j.castSucc)
              have hr := hdisj (s.index j.succ)
              omega))
      have heval : (∑ i ∈ F, jamesPathMap 𝕜 p s (x i).val) j =
          ∑ i ∈ F, jamesPathMap 𝕜 p s (x i).val j := by
        exact map_sum (PiLp.projₗ (𝕜 := 𝕜) p.val (fun _ : Fin s.length => 𝕜) j) _ F
      rw [heval]
      exact norm_sum_rpow_le_two_of_sparse F
        (fun i => jamesPathMap 𝕜 p s (x i).val j) hq hcard
    _ = 2 ^ (p.val.toReal - 1) *
        ∑ i ∈ F, ‖jamesPathMap 𝕜 p s (x i).val‖ ^ p.val.toReal := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (finitePiLp_norm_rpow p hp _).symm
    _ ≤ 2 ^ (p.val.toReal - 1) * ∑ i ∈ F, ‖x i‖ ^ p.val.toReal := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      exact Real.rpow_le_rpow (norm_nonneg _) ((x i).path_norm_le s) ENNReal.toReal_nonneg

include hp in
theorem james_norm_rpow_le_of_path {x : JamesSequenceSpace 𝕜 p} {C : ℝ} (hC : 0 ≤ C)
    (hpath : ∀ s : JamesPath, ‖jamesPathMap 𝕜 p s x.val‖ ^ p.val.toReal ≤ C) :
    ‖x‖ ^ p.val.toReal ≤ C := by
  have hq : 0 < p.val.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hC hq).mp
  apply JamesSequenceSpace.norm_le
  intro s
  exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hC hq).mpr (hpath s)

include hp in
/-- Upper lp power estimate for arbitrary finite families with disjoint supports. -/
theorem james_disjoint_norm_rpow_le (F : Finset ι) (x : ι → JamesSequenceSpace 𝕜 p)
    (hdisj : ∀ n : ℕ, (F.filter (fun i => x i n ≠ 0)).card ≤ 1) :
    ‖∑ i ∈ F, x i‖ ^ p.val.toReal ≤
      2 ^ (p.val.toReal - 1) * ∑ i ∈ F, ‖x i‖ ^ p.val.toReal :=
  james_norm_rpow_le_of_path p hp
    (mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)))
    (james_disjoint_path_rpow_le p hp F x hdisj)

end ThesisCommon
