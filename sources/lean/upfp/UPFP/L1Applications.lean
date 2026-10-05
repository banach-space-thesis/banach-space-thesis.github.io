import UPFP.PreservationTheorem
import UPFP.EllOneTheorem
import ThesisCommon.Analysis.AtomlessL1PrimaryFactorization

/-! Unconditional L1 applications of the preservation theorems. The
full finite-p Corollary 1.3 still requires the p>1 base-space theorem. -/
noncomputable section
open scoped ENNReal
namespace UPFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem corollary_6_2_L1_hasUPFP : HasUPFP 𝕜 (IntervalLp 𝕜 ⟨1, le_rfl⟩) :=
  intervalL1_hasUPFP 𝕜

theorem corollary_1_3_L1 :
    (HasUPFP 𝕜 (CZeroSum (IntervalLp 𝕜 ⟨1, le_rfl⟩)) ∧
      HasUPFP 𝕜 (EllInfinitySum (IntervalLp 𝕜 ⟨1, le_rfl⟩))) ∧
    (IsPrimary 𝕜 (CZeroSum (IntervalLp 𝕜 ⟨1, le_rfl⟩)) ∧
      IsPrimary 𝕜 (EllInfinitySum (IntervalLp 𝕜 ⟨1, le_rfl⟩))) :=
  theorem_1_2_finiteLpSelfSimilar (intervalL1_hasUPFP 𝕜)
    (intervalLpFunction_isFiniteLpSelfSimilar 𝕜 ⟨1, le_rfl⟩ (by simp))

theorem theorem_1_6_nat_upfp_primary :
    HasUPFP 𝕜 (EllOneSum ℕ (IntervalLp 𝕜 ⟨1, le_rfl⟩)) ∧
      IsPrimary 𝕜 (EllOneSum ℕ (IntervalLp 𝕜 ⟨1, le_rfl⟩)) :=
  theorem_1_1_selfSimilar (intervalL1_hasUPFP 𝕜)
    (intervalLpFunction_isSequenceSelfSimilar 𝕜 ⟨1, le_rfl⟩ (by simp))

theorem corollary_1_3_of_lp_base
    (hbase : ∀ p : BanachExponent, p.val ≠ ∞ → HasUPFP 𝕜 (IntervalLp 𝕜 p)) :
    Corollary_1_3 𝕜 := by
  constructor
  · intro p hp
    have h := theorem_1_2_finiteLpSelfSimilar (hbase p hp)
      (intervalLpFunction_isFiniteLpSelfSimilar 𝕜 p hp)
    exact ⟨h.1.2, h.2.2⟩
  · exact ⟨corollary_1_3_L1.1.1, corollary_1_3_L1.2.1⟩

end UPFP
