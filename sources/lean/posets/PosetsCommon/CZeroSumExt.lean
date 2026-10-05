import PosetsCommon.CZeroSumTruncation

noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {P Q : Type*}
  {X : P → Type*} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  {Z : Q → Type*} [∀ q, NormedAddCommGroup (Z q)] [∀ q, NormedSpace 𝕜 (Z q)]

/-- Operators on the genuine c₀ sums are determined by all of their blocks. -/
theorem operator_eq_of_blocks_eq {S T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z}
    (h : ∀ s t, operatorBlock 𝕜 X Z S s t = operatorBlock 𝕜 X Z T s t) : S = T := by
  have hinj (t : P) (x : X t) : S (sumInjection 𝕜 X t x) = T (sumInjection 𝕜 X t x) := by
    apply Subtype.ext
    apply lp.ext
    funext s
    exact congrArg (fun b : X t →L[𝕜] Z s => b x) (h s t)
  apply ContinuousLinearMap.ext
  intro x
  have htrunc (F : Finset P) :
      S (finiteProjection 𝕜 X F x) = T (finiteProjection 𝕜 X F x) := by
    simp only [finiteProjection, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact hinj t (sumProjection 𝕜 X t x)
  have hS := S.continuous.continuousAt.tendsto.comp (finiteProjection_tendsto 𝕜 X x)
  have hT := T.continuous.continuousAt.tendsto.comp (finiteProjection_tendsto 𝕜 X x)
  exact tendsto_nhds_unique hS (hT.congr' (Eventually.of_forall (fun F => (htrunc F).symm)))

end ThesisCommon
