import SurveyStatements.P4FiniteExtension
import Mathlib.Analysis.Normed.Operator.Prod

/-! The actual finite extension splits as the original block and its kernel. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SurveyStatements.P4.FiniteBasisExtension

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (G : FiniteBasisExtension 𝕜 E)

lemma retraction_embedding (x : E) : G.retraction (G.embedding x) = x :=
  congrArg (fun A : E →L[𝕜] E => A x) G.retraction_comp_embedding

def splitLinearEquiv : G.Carrier ≃ₗ[𝕜] E × G.Complement where
  toFun x := (G.retraction x, ⟨x - G.embedding (G.retraction x), by
    change G.retraction (x - G.embedding (G.retraction x)) = 0
    rw [map_sub, retraction_embedding, sub_self]⟩)
  invFun p := G.embedding p.1 + p.2.val
  left_inv x := by simp
  right_inv p := by
    apply Prod.ext
    · change G.retraction (G.embedding p.1 + p.2.val) = p.1
      rw [map_add, retraction_embedding, (show G.retraction p.2.val = 0 from p.2.property),
        add_zero]
    · apply Subtype.ext
      change G.embedding p.1 + p.2.val -
        G.embedding (G.retraction (G.embedding p.1 + p.2.val)) = p.2.val
      rw [map_add, retraction_embedding,
        (show G.retraction p.2.val = 0 from p.2.property), add_zero, add_sub_cancel_left]
  map_add' x y := by
    apply Prod.ext
    · exact G.retraction.map_add x y
    · apply Subtype.ext
      change x + y - G.embedding (G.retraction (x + y)) =
        (x - G.embedding (G.retraction x)) + (y - G.embedding (G.retraction y))
      simp only [map_add]
      abel
  map_smul' a x := by
    apply Prod.ext
    · exact G.retraction.map_smul a x
    · apply Subtype.ext
      change a • x - G.embedding (G.retraction (a • x)) =
        a • (x - G.embedding (G.retraction x))
      simp only [map_smul, smul_sub]

lemma norm_splitLinearEquiv_le (x : G.Carrier) : ‖G.splitLinearEquiv x‖ ≤ 3 * ‖x‖ := by
  have hQ : ‖G.retraction x‖ ≤ ‖x‖ :=
    (G.retraction.le_opNorm x).trans (by nlinarith [G.norm_retraction_le, norm_nonneg x])
  have hJ : ‖G.embedding (G.retraction x)‖ ≤ 2 * ‖x‖ := by
    calc
      ‖G.embedding (G.retraction x)‖ ≤ ‖G.embedding‖ * ‖G.retraction x‖ :=
        G.embedding.le_opNorm _
      _ ≤ 2 * ‖x‖ := mul_le_mul G.norm_embedding_le hQ (norm_nonneg _) (by norm_num)
  change max ‖G.retraction x‖ ‖x - G.embedding (G.retraction x)‖ ≤ 3 * ‖x‖
  apply max_le
  · nlinarith [norm_nonneg x]
  · exact (norm_sub_le _ _).trans (by linarith)

lemma norm_splitLinearEquiv_symm_le (p : E × G.Complement) :
    ‖G.splitLinearEquiv.symm p‖ ≤ 3 * ‖p‖ := by
  change ‖G.embedding p.1 + p.2.val‖ ≤ 3 * ‖p‖
  have hJ : ‖G.embedding p.1‖ ≤ 2 * ‖p‖ := by
    calc
      ‖G.embedding p.1‖ ≤ ‖G.embedding‖ * ‖p.1‖ := G.embedding.le_opNorm _
      _ ≤ 2 * ‖p‖ := mul_le_mul G.norm_embedding_le (norm_fst_le p)
        (norm_nonneg _) (by norm_num)
  have hH : ‖p.2.val‖ ≤ ‖p‖ := norm_snd_le p
  exact (norm_add_le _ _).trans (by linarith)

def splitContinuousLinearEquiv : G.Carrier ≃L[𝕜] E × G.Complement :=
  G.splitLinearEquiv.toContinuousLinearEquivOfBounds 3 3
    G.norm_splitLinearEquiv_le G.norm_splitLinearEquiv_symm_le

end SurveyStatements.P4.FiniteBasisExtension
