import CKEUPFP.Definitions

/-!
# Initial vocabulary for Section 3

The operator field `A` is an explicit argument below. Constructing it from
representing measures, and proving its properties, remain later proof tasks.
-/

noncomputable section

universe u v w

namespace CKEUPFP

variable {𝕜 : Type u} [RCLike 𝕜]
variable {K : Type v} [TopologicalSpace K]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Strong continuity means continuity after applying each fixed vector.
It does not require continuity in the operator norm. -/
def IsStronglyContinuous (A : K → E →L[𝕜] E) : Prop :=
  ∀ x : E, Continuous (fun t => A t x)

/-- The uniform operator-norm bound on a field, used in Section 2. -/
def IsUniformlyBounded (A : K → E →L[𝕜] E) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t : K, ‖A t‖ ≤ M

variable [CompactSpace K]

/-- The row operator `δ_t ∘ T` from the beginning of Section 3. -/
def rowOperator (T : C(K, E) →L[𝕜] C(K, E)) (t : K) : C(K, E) →L[𝕜] E :=
  (ContinuousMap.evalCLM 𝕜 t).comp T

/-- Functions that vanish off `O`. This is the paper's exact condition;
no closure-of-support condition is imposed. -/
def VanishesOff (O : Set K) (f : C(K, E)) : Prop :=
  ∀ s : K, s ∉ O → f s = 0

/-- Definition `def:local-defect`, with its operator field supplied explicitly.
The paper uses this for open `O` and `t ∈ O`. The formula is meaningful for any
`O,t`: the defining set contains zero and is bounded above by `‖T‖ + ‖A t‖`.
Those bounds and the representing-measure identification are not proved here. -/
def localDefect (T : C(K, E) →L[𝕜] C(K, E))
    (A : K → E →L[𝕜] E) (O : Set K) (t : K) : ℝ :=
  sSup {r : ℝ | ∃ f : C(K, E), ‖f‖ ≤ 1 ∧ VanishesOff O f ∧
    r = ‖T f t - A t (f t)‖}

end CKEUPFP
