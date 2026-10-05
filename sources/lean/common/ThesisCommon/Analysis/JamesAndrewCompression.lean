import ThesisCommon.Analysis.JamesOperatorPrefixLimits
import ThesisCommon.Analysis.JamesPrefixSubsequence
import ThesisCommon.Analysis.JamesAndrewWeights
import ThesisCommon.Analysis.JamesSummableDiagonal

/-! Operators whose actual bidual scalar is one have a sampling/repetition
compression within one half of the identity in operator norm. All matrices,
diagonal corrections, and errors arise from the given operator. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ⊤)
  (hpl : 1 < p.val.toReal)

theorem exists_james_small_prefix_compression
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (hscalar : jamesOperatorScalar p hp hpl T = 1) :
    ∃ (α β : ℕ → ℕ) (hα : StrictMono α) (hβ : StrictMono β),
      ‖((jamesSample (𝕜 := 𝕜) p hp α hα).comp T).comp
        (jamesPrefixRepeat (𝕜 := 𝕜) p hp β hβ) - ContinuousLinearMap.id 𝕜 _‖ < 1 / 2 := by
  obtain ⟨α, β, hα, hβ, hdiag, hmatrix⟩ :=
    jamesOperatorPrefix_selected_matrix p hp hpl T jamesAndrewWeight jamesAndrewWeight_pos
  rw [hscalar] at hdiag
  let a : ℕ → 𝕜 := fun i => jamesOperatorPrefixLimit p hp hpl T (α i) - 1
  have ha : Summable (fun i => ‖a i‖) :=
    jamesAndrewWeight_summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => (hdiag i).le)
  let D := jamesSummableDiagonal p hp a
  have hD : ‖D‖ ≤ (1 / 32 : ℝ) := by
    calc
      ‖D‖ ≤ 2 * ∑' i, ‖a i‖ := norm_jamesSummableDiagonal_le p hp a ha
      _ ≤ 2 * ∑' i, jamesAndrewWeight i :=
        mul_le_mul_of_nonneg_left
          (ha.tsum_le_tsum (fun i => (hdiag i).le) jamesAndrewWeight_summable) (by norm_num)
      _ = _ := by rw [jamesAndrewWeight_tsum]; norm_num
  let B := ((jamesSample (𝕜 := 𝕜) p hp α hα).comp T).comp
    (jamesPrefixRepeat (𝕜 := 𝕜) p hp β hβ)
  let A := B - ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p) - D
  have hcoord (i j : ℕ) : ‖A (jamesConstantPrefix p hp j) i‖ ≤
      jamesAndrewWeight i * jamesAndrewWeight j := by
    have he : A (jamesConstantPrefix p hp j) i = T (jamesConstantPrefix p hp (β j)) (α i) -
        (if i ≤ j then jamesOperatorPrefixLimit p hp hpl T (α i) else 0) := by
      simp only [A, B, D, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        JamesSequenceSpace.sub_apply, ContinuousLinearMap.id_apply, jamesSample_apply,
        jamesPrefixRepeat_prefix, jamesSummableDiagonal_apply p hp a ha,
        jamesConstantPrefix_apply]
      dsimp only [a]
      split_ifs <;> ring
    rw [he]
    exact (hmatrix i j).le
  have hcol (j : ℕ) : ‖A (jamesConstantPrefix p hp j)‖ ≤ (1 / 32 : ℝ) * jamesAndrewWeight j := by
    have hb := james_norm_le_two_tsum_of_coordinates p hp (A (jamesConstantPrefix p hp j))
      (fun i => jamesAndrewWeight i * jamesAndrewWeight j)
      (jamesAndrewWeight_summable.mul_right _)
      (fun i => mul_nonneg (jamesAndrewWeight_pos i).le (jamesAndrewWeight_pos j).le)
      (fun i => hcoord i j)
    rw [tsum_mul_right, jamesAndrewWeight_tsum] at hb
    convert hb using 1
    ring
  have hs : Summable (fun j => ‖A (jamesConstantPrefix p hp j)‖) :=
    (jamesAndrewWeight_summable.mul_left (1 / 32)).of_nonneg_of_le
      (fun _ => norm_nonneg _) hcol
  have hA : ‖A‖ ≤ (1 / 1024 : ℝ) := by
    calc
      ‖A‖ ≤ 2 * ∑' j, ‖A (jamesConstantPrefix p hp j)‖ :=
        james_operator_norm_le_two_tsum_summing_columns p hp A hs
      _ ≤ 2 * ∑' j, (1 / 32 : ℝ) * jamesAndrewWeight j :=
        mul_le_mul_of_nonneg_left
          (hs.tsum_le_tsum hcol (jamesAndrewWeight_summable.mul_left _)) (by norm_num)
      _ = _ := by rw [tsum_mul_left, jamesAndrewWeight_tsum]; norm_num
  refine ⟨α, β, hα, hβ, ?_⟩
  change ‖B - ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p)‖ < 1 / 2
  have he : B - ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p) = A + D := by
    dsimp only [A]
    abel
  rw [he]
  exact (norm_add_le _ _).trans_lt (by linarith)

end ThesisCommon
