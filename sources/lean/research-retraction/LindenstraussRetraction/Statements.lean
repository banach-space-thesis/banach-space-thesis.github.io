import LindenstraussRetraction.SchauderBasis

/-!
# Statement targets for the supplied paper

Every `...Statement` below is a definition of a proposition, NOT a proof of it.
The proofs are supplied separately by MainTheorem, ComplementedTransfer,
RadialRetraction and Correction. No target definition assumes its own truth.
-/

noncomputable section

namespace LindenstraussRetraction

universe u v w

/-- A bundled separable Banach space, used to quantify over the space in the
existence statements. Completeness and separability concern the norm topology. -/
structure SeparableBanachSpace (𝕜 : Type v) [RCLike 𝕜] where
  Carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace 𝕜 Carrier]
  [completeSpace : CompleteSpace Carrier]
  [separableSpace : TopologicalSpace.SeparableSpace Carrier]

attribute [instance] SeparableBanachSpace.normedAddCommGroup
  SeparableBanachSpace.normedSpace SeparableBanachSpace.completeSpace
  SeparableBanachSpace.separableSpace

variable (𝕜 : Type v) [RCLike 𝕜]

/-- The core assertion of `thm:main` in `1-Introduction.tex`. -/
def MainUnitBallStatement : Prop :=
  ∃ X : SeparableBanachSpace.{0, v} 𝕜,
    HasBimonotoneSchauderBasis 𝕜 X.Carrier ∧
      ¬ HasUniformUnitBallBidualRetraction 𝕜 X.Carrier

/-- The complete main statement, including both "in particular" conclusions
for the SAME witness space. This is a target proposition, not a theorem. -/
def MainStatement : Prop :=
  ∃ X : SeparableBanachSpace.{0, v} 𝕜,
    HasBimonotoneSchauderBasis 𝕜 X.Carrier ∧
      (¬ HasUniformUnitBallBidualRetraction 𝕜 X.Carrier) ∧
      (¬ HasUniformBidualRetraction 𝕜 X.Carrier) ∧
      (¬ HasLipschitzBidualRetraction 𝕜 X.Carrier)

/-- The auxiliary existence target from `prop:auxiliary-space`.
ConcreteConstruction defines its explicit `c₀`-sum witness. -/
def AuxiliarySpaceStatement : Prop :=
  ∃ W : SeparableBanachSpace.{0, v} 𝕜,
    Nonempty (MonotoneFDD 𝕜 W.Carrier) ∧
      ¬ HasUniformUnitBallBidualRetraction 𝕜 W.Carrier

section Transfer

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (Z : Type w) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- `lem:complemented-transfer`: uniform ball retractability passes to a
complemented subspace. Its failure therefore passes to the containing space. -/
def ComplementedTransferStatement [CompleteSpace E] [CompleteSpace Z] : Prop :=
  IsComplementedIn 𝕜 E Z →
    HasUniformUnitBallBidualRetraction 𝕜 Z →
      HasUniformUnitBallBidualRetraction 𝕜 E

/-- The radial-retraction implication used at the end of the main proof. -/
def WholeSpaceToUnitBallStatement [CompleteSpace E] : Prop :=
  HasUniformBidualRetraction 𝕜 E → HasUniformUnitBallBidualRetraction 𝕜 E

end Transfer

section Correction

variable {𝕜}
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (W : Type w) [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- `lem:correction`. The bound is explicit, and the error threshold is
strictly below one. The sphere is the domain of the approximate section;
the resulting exact section is defined on the closed ball. -/
def CorrectionStatement [CompleteSpace E] [CompleteSpace W] : Prop :=
  ∀ q : E →L[𝕜] W, IsNormQuotient q →
    ∀ φ : UnitSphere W → E, UniformContinuous φ →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖φ x‖ ≤ C) →
      ∀ errorBound : ℝ, 0 ≤ errorBound → errorBound < 1 →
        (∀ x : UnitSphere W, ‖q (φ x) - x.val‖ ≤ errorBound) →
          HasUniformSectionOnUnitBall q

end Correction

/-- The elementary implication between the two whole-space notions is proved. -/
theorem hasLipschitzBidualRetraction_implies_uniform
    (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (h : HasLipschitzBidualRetraction 𝕜 X) : HasUniformBidualRetraction 𝕜 X :=
  HasLipschitzRetraction.hasUniformRetraction h

end LindenstraussRetraction
