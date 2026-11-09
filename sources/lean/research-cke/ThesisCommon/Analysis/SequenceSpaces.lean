import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Order.Compact
import ThesisCommon.Analysis.Primary

/-! Actual spaces appearing in the two primariness manuscripts.
`lp` uses summability for finite p and boundedness for p = ∞.
`C₀(ℕ,X)` is the vector-valued null-sequence space with supremum norm.
-/
noncomputable section
open scoped ZeroAtInfty ENNReal
universe u v
namespace ThesisCommon

/-- The complete range of outer exponents [1,∞], including both endpoints. -/
abbrev BanachExponent := {p : ℝ≥0∞ // 1 ≤ p}

instance (p : BanachExponent) : Fact (1 ≤ p.val) := ⟨p.property⟩

abbrev SequenceSum (p : BanachExponent) (X : Type v) [NormedAddCommGroup X] :=
  lp (fun _ : ℕ => X) p.val

abbrev EllOneSum (Γ : Type u) (X : Type v) [NormedAddCommGroup X] :=
  lp (fun _ : Γ => X) 1

abbrev EllInfinitySum (X : Type v) [NormedAddCommGroup X] :=
  lp (fun _ : ℕ => X) ∞

abbrev CZeroSum (X : Type v) [NormedAddCommGroup X] := C₀(ℕ, X)

/-- The actual closed ordinal interval [0,α] with order/subspace topology. -/
abbrev OrdinalInterval (α : Ordinal.{u}) := Set.Icc (0 : Ordinal.{u}) α

abbrev OrdinalContinuous (𝕜 : Type*) [RCLike 𝕜] (α : Ordinal.{u}) :=
  C(OrdinalInterval α, 𝕜)

abbrev UnitInterval := Set.Icc (0 : ℝ) 1
abbrev IntervalContinuous (𝕜 : Type*) [RCLike 𝕜] := C(UnitInterval, 𝕜)

/-- Scalar Lp[0,1], as a.e. equivalence classes for restricted Lebesgue measure.
The underlying domain is ℝ with measure supported on [0,1]. -/
abbrev IntervalLp (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :=
  MeasureTheory.Lp 𝕜 p.val (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- UPFP paper, Theorem 1.1(i): p may be ∞; the c₀ alternative is included. -/
def IsSequenceSelfSimilar : Prop :=
  (∃ p : BanachExponent, Nonempty (X ≃L[𝕜] SequenceSum p X)) ∨
    Nonempty (X ≃L[𝕜] CZeroSum X)

/-- UPFP paper, Theorem 1.2(i): finite p only, with no c₀ alternative. -/
def IsFiniteLpSelfSimilar : Prop :=
  ∃ p : BanachExponent, p.val ≠ ∞ ∧ Nonempty (X ≃L[𝕜] SequenceSum p X)

end ThesisCommon
