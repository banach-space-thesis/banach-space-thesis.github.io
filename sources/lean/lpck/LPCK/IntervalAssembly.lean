import LPCK.MainStatements
import ThesisCommon.Analysis.IntervalLpAssembly
import ThesisCommon.Analysis.IntervalCZeroEquiv
import ThesisCommon.Analysis.IntervalPrimariness

/-! All sequence-space arguments of LPCK Theorem 1.2. The original target
is proved without extra hypotheses. Its base-space argument uses the checked
diagonal-atom localization proof; the separate source-specific Weis bound
remains an open proof-method obligation. -/
noncomputable section
namespace LPCK
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

alias lemma_4_3_unitInterval := ThesisCommon.interval_infinity_upper_selection
alias lemma_4_4_unitInterval := ThesisCommon.interval_infinity_lower_diagonal_blocks
alias proposition_4_6_unitInterval := ThesisCommon.interval_infinity_lower_dichotomy

theorem theorem_1_2_of_base_results
    (hX : HasUPFP 𝕜 (IntervalContinuous 𝕜))
    (e : IntervalContinuous 𝕜 ≃L[𝕜] CZeroSum (IntervalContinuous 𝕜))
    (p : BanachExponent) : Theorem_1_2 𝕜 p :=
  hX.interval_lp e p.val

theorem theorem_1_2_of_base_upfp
    (hX : HasUPFP 𝕜 (IntervalContinuous 𝕜))
    (p : BanachExponent) : Theorem_1_2 𝕜 p :=
  theorem_1_2_of_base_results hX intervalCZeroEquiv p

/-- The original all-exponent statement. The base-space proof route is
documented in IntervalPrimariness and the proof-method correspondence. -/
theorem theorem_1_2_proof (p : BanachExponent) : Theorem_1_2 𝕜 p :=
  theorem_1_2_of_base_upfp interval_hasUPFP p

end LPCK
