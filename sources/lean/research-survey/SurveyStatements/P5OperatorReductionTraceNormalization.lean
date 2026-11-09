import SurveyStatements.P5OperatorReductionRegisteredTraces
import SurveyStatements.P5OperatorReductionConcreteSteps

/-! Parent normalization preserves equality of actual dyadic trace sets. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def normalizedParentTrace (v : LpHaarDyadicSetIndex → 𝕜)
    (P : LpHaarFiniteParent) : 𝕜 :=
  (unitIntervalMeasure.real P.set : 𝕜)⁻¹ * v ⟨P.level, P.atoms⟩

theorem normalizedParentTrace_equal_sets (v : LpHaarDyadicSetIndex → 𝕜)
    (hv : ∀ i j, lpHaarDyadicSet i = lpHaarDyadicSet j → v i = v j)
    (P Q : LpHaarFiniteParent) (hPQ : P.set = Q.set) :
    normalizedParentTrace v P = normalizedParentTrace v Q := by
  have hvalue : v ⟨P.level, P.atoms⟩ = v ⟨Q.level, Q.atoms⟩ :=
    hv _ _ hPQ
  unfold normalizedParentTrace
  rw [hPQ, hvalue]

def normalizedRegisteredBlockTrace
    {d : (LpHaarFiniteSplit × LpHaarFiniteSplit) → ∀ n, Fin (2 ^ n) → 𝕜}
    {r : ℕ → ℕ} {M : (LpHaarFiniteSplit × LpHaarFiniteSplit) → ℝ}
    (a : ∀ pair, RegisteredDyadicTrace (d pair) r (M pair)) : NormalizedBlockTrace 𝕜 :=
  fun pair => normalizedParentTrace (a pair).value

theorem normalizedRegisteredBlockTrace_equal_sets
    {d : (LpHaarFiniteSplit × LpHaarFiniteSplit) → ∀ n, Fin (2 ^ n) → 𝕜}
    {r : ℕ → ℕ} {M : (LpHaarFiniteSplit × LpHaarFiniteSplit) → ℝ}
    (a : ∀ pair, RegisteredDyadicTrace (d pair) r (M pair))
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit)
    (P Q : LpHaarFiniteParent) (hPQ : P.set = Q.set) :
    normalizedRegisteredBlockTrace a pair P = normalizedRegisteredBlockTrace a pair Q :=
  normalizedParentTrace_equal_sets (a pair).value (a pair).equal_sets P Q hPQ

end SurveyStatements.P5OperatorReduction
