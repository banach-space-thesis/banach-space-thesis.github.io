import ThesisCommon.Analysis.JamesTreeConcreteFiniteColumnDichotomy
import ThesisCommon.Analysis.JamesTreeFiniteColumnFactorization

/-! Uniform factorisation on both actual James-tree completions. The finite
column dichotomy is proved by the operator-dependent tree selection, then
the genuine small operator perturbation gives the bound twelve. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}

theorem literalJamesTree_hasCPFP_twelve (hp : 1 < p.val.toReal) :
    HasCPFP 𝕜 (LiteralChainJamesTreeSpace 𝕜 p) 12 :=
  jamesTree_hasCPFP_twelve_of_finite_column_dichotomy
    literalJamesTreeMaskClosed_levels
    (fun T N hN hT hcompl =>
      literalJamesTree_finite_column_factor_dichotomy hp T N hN hT hcompl)

theorem consecutiveJamesTree_hasCPFP_twelve (hp : 1 < p.val.toReal) :
    HasCPFP 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p) 12 :=
  jamesTree_hasCPFP_twelve_of_finite_column_dichotomy
    consecutiveJamesTreeMaskClosed_levels
    (fun T N hN hT hcompl =>
      consecutiveJamesTree_finite_column_factor_dichotomy hp T N hN hT hcompl)

theorem literalJamesTree_hasUPFP (hp : 1 < p.val.toReal) :
    HasUPFP 𝕜 (LiteralChainJamesTreeSpace 𝕜 p) :=
  ⟨12, by norm_num, literalJamesTree_hasCPFP_twelve hp⟩

theorem consecutiveJamesTree_hasUPFP (hp : 1 < p.val.toReal) :
    HasUPFP 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p) :=
  ⟨12, by norm_num, consecutiveJamesTree_hasCPFP_twelve hp⟩

end ThesisCommon
