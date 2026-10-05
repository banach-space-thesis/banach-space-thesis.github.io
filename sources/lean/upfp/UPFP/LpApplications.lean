import UPFP.L1Applications
import UPFP.L2Applications
import ThesisCommon.Analysis.IntervalLpUniformFactorization

/-! The original all-finite-exponent Corollary 1.3. The actual interval
Lp base UPFP is proved by the Alspach--Enflo--Odell Haar-block construction. -/
noncomputable section
open scoped ENNReal
namespace UPFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem corollary_1_3_of_remaining_lp_base
    (hbase : ∀ p : BanachExponent, p.val ≠ ∞ → p.val ≠ 1 → p.val ≠ 2 →
      HasUPFP 𝕜 (IntervalLp 𝕜 p)) : Corollary_1_3 𝕜 := by
  apply corollary_1_3_of_lp_base
  intro p hp
  by_cases h1 : p.val = 1
  · have he : p = ⟨1, le_rfl⟩ := Subtype.ext h1
    rw [he]
    exact intervalL1_hasUPFP 𝕜
  by_cases h2 : p.val = 2
  · have he : p = ⟨2, by norm_num⟩ := Subtype.ext h2
    rw [he]
    exact intervalL2_hasUPFP 𝕜
  exact hbase p hp h1 h2

theorem corollary_1_3_proof : Corollary_1_3 𝕜 :=
  corollary_1_3_of_lp_base (fun p hp => intervalLp_hasUPFP 𝕜 p hp)

end UPFP
