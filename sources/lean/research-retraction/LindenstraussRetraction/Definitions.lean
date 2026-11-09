import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Retractions and the bidual

Definitions for Antonio Acuaviva's supplied manuscript, especially Section 2
and Theorem `thm:main`. The scalar field is real or complex (`RCLike`).
Retractions are arbitrary functions satisfying a left-inverse identity;
no linearity is imposed on them.
-/

noncomputable section

open scoped NNReal ENNReal

namespace LindenstraussRetraction

universe u v w

/-- The closed unit ball, with its inherited metric and uniform structure. -/
abbrev UnitBall (X : Type u) [NormedAddCommGroup X] := {x : X // ‖x‖ ≤ 1}

/-- The unit sphere, with its inherited metric and uniform structure. -/
abbrev UnitSphere (X : Type u) [NormedAddCommGroup X] := {x : X // ‖x‖ = 1}

/-- `r` retracts along the specified inclusion `i`: `r (i x) = x`.
Specifying `i` avoids silently choosing a different copy of the smaller space. -/
def IsRetraction {A : Type u} {B : Type v} (i : A → B) (r : B → A) : Prop :=
  Function.LeftInverse r i

/-- Uniform retractability along a specified inclusion. -/
def HasUniformRetraction {A : Type u} {B : Type v}
    [UniformSpace A] [UniformSpace B] (i : A → B) : Prop :=
  ∃ r : B → A, UniformContinuous r ∧ IsRetraction i r

/-- Lipschitz retractability with some finite nonnegative constant. -/
def HasLipschitzRetraction {A : Type u} {B : Type v}
    [PseudoMetricSpace A] [PseudoMetricSpace B] (i : A → B) : Prop :=
  ∃ (K : ℝ≥0) (r : B → A), LipschitzWith K r ∧ IsRetraction i r

theorem HasLipschitzRetraction.hasUniformRetraction
    {A : Type u} {B : Type v} [PseudoMetricSpace A] [PseudoMetricSpace B]
    {i : A → B} (h : HasLipschitzRetraction i) : HasUniformRetraction i := by
  obtain ⟨K, r, hr, hri⟩ := h
  exact ⟨r, hr.uniformContinuous, hri⟩

section Bidual

variable (𝕜 : Type v) [RCLike 𝕜]
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The continuous bidual with its operator norm; not the algebraic dual. -/
abbrev Bidual := StrongDual 𝕜 (StrongDual 𝕜 X)

/-- The canonical evaluation embedding `J_X : X → X**`. -/
def bidualEmbedding : X →ₗᵢ[𝕜] Bidual 𝕜 X :=
  NormedSpace.inclusionInDoubleDualLi 𝕜

@[simp] theorem bidualEmbedding_apply (x : X) (f : StrongDual 𝕜 X) :
    bidualEmbedding 𝕜 X x f = f x := rfl

/-- The canonical embedding restricted to the closed unit balls. -/
def unitBallBidualEmbedding : UnitBall X → UnitBall (Bidual 𝕜 X) :=
  fun x => ⟨bidualEmbedding 𝕜 X x, by
    simpa only [(bidualEmbedding 𝕜 X).norm_map] using x.property⟩

/-- There exists a uniformly continuous retraction `X** → X` fixing `J_X(X)`. -/
def HasUniformBidualRetraction : Prop :=
  HasUniformRetraction (bidualEmbedding 𝕜 X)

/-- There exists a Lipschitz retraction `X** → X` fixing `J_X(X)`. -/
def HasLipschitzBidualRetraction : Prop :=
  HasLipschitzRetraction (bidualEmbedding 𝕜 X)

/-- There exists a uniformly continuous retraction `B_(X**) → B_X`.
The codomain is the ball itself, so the range constraint is explicit. -/
def HasUniformUnitBallBidualRetraction : Prop :=
  HasUniformRetraction (unitBallBidualEmbedding 𝕜 X)

/-- Section 2, `def:retraction-constant`: the bidual Lipschitz retraction constant.
Taking the infimum in `ℝ≥0∞` makes the empty infimum `∞`. Infimizing over
all admissible Lipschitz bounds also avoids assuming the optimum is attained. -/
def bidualLipschitzRetractionConstant : ℝ≥0∞ :=
  sInf {L : ℝ≥0∞ | ∃ (K : ℝ≥0) (r : Bidual 𝕜 X → X),
    L = (K : ℝ≥0∞) ∧ LipschitzWith K r ∧ IsRetraction (bidualEmbedding 𝕜 X) r}

end Bidual

section Quotients

variable {𝕜 : Type w} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The paper's isometric quotient convention, using the equivalent open-ball
formulation stated in Section 2. Surjectivity alone would be insufficient. -/
def IsNormQuotient (q : E →L[𝕜] W) : Prop :=
  q '' Metric.ball (0 : E) 1 = Metric.ball (0 : W) 1

/-- A uniformly continuous section of `q` on the closed unit ball of `W`.
The section takes values in all of `E`, without a unit-ball range constraint. -/
def HasUniformSectionOnUnitBall (q : E →L[𝕜] W) : Prop :=
  ∃ s : UnitBall W → E, UniformContinuous s ∧ ∀ x, q (s x) = x.val

/-- `E` is linearly complemented in `Z`, expressed by a bounded linear
embedding and a bounded linear left inverse. -/
def IsComplementedIn (𝕜 : Type w) [RCLike 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Z : Type v) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] : Prop :=
  ∃ (U : E →L[𝕜] Z) (V : Z →L[𝕜] E), Function.LeftInverse V U

end Quotients

end LindenstraussRetraction
