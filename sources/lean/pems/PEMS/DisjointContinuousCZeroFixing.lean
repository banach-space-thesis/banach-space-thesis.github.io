import PEMS.CZeroFixingUpperBound
import ThesisCommon.Analysis.CZeroQuantitativeSubcopy
import ThesisCommon.Analysis.ContinuousMapCZeroBlocks

/-! Actual disjoint continuous columns give the sharp c₀-fixing lower
bound. Both the c₀ synthesis and its bounded-below subcopy are constructed. -/
noncomputable section
open Set ThesisCommon
namespace PEMS
variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem le_fixesCZeroSup_of_column_lower_bound
    (T : E →L[𝕜] F) (V : CZero 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1)
    {c : ℝ} (hc : 0 < c) (hcol : ∀ n, c ≤ ‖T (V (cZeroSingle n 1))‖) :
    c ≤ fixesCZeroSup T := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨A, hA, hlow⟩ := exists_cZero_subcopy_of_column_lower_bound (T.comp V) hc hcol hε
  let W := V.comp A
  have hW : ‖W‖ ≤ 1 := (V.opNorm_comp_le A).trans
    ((mul_le_mul hV hA (norm_nonneg A) zero_le_one).trans_eq (one_mul 1))
  have hl : c-ε ≤ minimumModulus (T.comp W) := by
    apply le_csInf
    · exact ⟨_, ⟨cZeroSingle 0 1, (scalarCZeroSchauderBasis (𝕜 := 𝕜)).norm_vector 0, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      have h := hlow x
      simpa only [hx, mul_one] using h
  have hu : minimumModulus (T.comp W) ≤ fixesCZeroSup T := by
    apply le_csSup
    · refine ⟨dualWeakEssentialNorm T, ?_⟩
      rintro _ ⟨B, hB, rfl⟩
      exact minimumModulus_comp_le_dualWeakEssentialNorm T B hB
    · exact ⟨W, hW, rfl⟩
  linarith

variable {L : Type*} [TopologicalSpace L] [CompactSpace L]

theorem le_fixesCZeroSup_of_disjoint_continuous_columns
    (T : C(L, 𝕜) →L[𝕜] F) (f : ℕ → C(L, 𝕜))
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hdis : Pairwise fun i j => ∀ t, f i t = 0 ∨ f j t = 0)
    {c : ℝ} (hc : 0 < c) (hTf : ∀ n, c ≤ ‖T (f n)‖) :
    c ≤ fixesCZeroSup T := by
  let G (n : ℕ) := (ContinuousLinearMap.id 𝕜 𝕜).smulRight (f n)
  have hG (n : ℕ) : ‖G n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change ‖a • f n‖ ≤ 1*‖a‖
    rw [norm_smul, one_mul]
    exact (mul_le_mul_of_nonneg_left (hf n) (norm_nonneg a)).trans_eq (mul_one _)
  have hd (i j : ℕ) (hij : i≠j) (a b : 𝕜) (t : L) :
      G i a t = 0 ∨ G j b t = 0 := by
    change a*f i t = 0 ∨ b*f j t = 0
    rcases hdis hij t with h | h
    · exact Or.inl (by rw [h, mul_zero])
    · exact Or.inr (by rw [h, mul_zero])
  let V := continuousMapCZeroInsert G hG hd
  have hV : ‖V‖ ≤ 1 := norm_continuousMapCZeroInsert_le ..
  apply le_fixesCZeroSup_of_column_lower_bound T V hV hc
  intro n
  have heq : V (cZeroSingle n 1) = f n := by
    rw [show V = continuousMapCZeroInsert G hG hd from rfl, continuousMapCZeroInsert_single]
    simp [G]
  rw [heq]
  exact hTf n

end PEMS
