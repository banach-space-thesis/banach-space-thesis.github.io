import CKEUPFP.Definitions
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.Compact

/-!
# Statements of the main results

Each declaration in this file defines a proposition, keeping the statements
separate from their proofs. `Transfer.lean`, `CantorTransfer.lean`, and
`MixedCorollary.lean` prove these propositions. No paper result is added as an
axiom.
-/

noncomputable section

universe u v w

namespace CKEUPFP

open scoped ENNReal

variable (𝕜 : Type u) [RCLike 𝕜]

/-- Theorem 1.1 (`thm:transfer`), with all its hypotheses.
`C(K,E)` is mathlib's space of continuous functions with its supremum norm.
Metrizability is a property of the given topology; no metric is chosen. -/
def TransferTheorem
    (K : Type v) [TopologicalSpace K] [CompactSpace K] [TopologicalSpace.MetrizableSpace K]
    [Uncountable K]
    (E : Type w) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] : Prop :=
  ContainsNoCZero 𝕜 E → HasUPFP 𝕜 E → HasUPFP 𝕜 C(K, E)

/-- Binary sequences with their product topology, a standard model of the
Cantor set. This is an actual compact space, not an abstract placeholder. -/
abbrev CantorSpace := ℕ → Fin 2

/-- The quantitative assertion proved in Section 4 after reducing to the
Cantor set: `C`-PFP transfers to `(4C/3)`-PFP. This bound is not asserted for
arbitrary compact metrizable `K`, since the isomorphic reduction changes norms. -/
def CantorQuantitativeTransfer
    (E : Type w) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] : Prop :=
  ContainsNoCZero 𝕜 E → ∀ C : ℝ,
    HasCPFP 𝕜 E C → HasCPFP 𝕜 C(CantorSpace, E) (4 * C / 3)

/-- The exponent range in Corollary 1.2: `1 ≤ p < ∞`, including `p = 1`. -/
abbrev FiniteBanachExponent := {p : ℝ≥0∞ // 1 ≤ p ∧ p < ⊤}

instance (p : FiniteBanachExponent) : Fact (1 ≤ p.val) := ⟨p.property.1⟩

/-- Scalar `ℓ_p` over the natural numbers, using the actual `lp` norm. -/
abbrev ScalarEllp (p : FiniteBanachExponent) := lp (fun _ : ℕ => 𝕜) p.val

/-- The closed real interval `[0,1]` with its subspace topology. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- The classical `L_p[0,1]`, using a.e. equivalence classes for Lebesgue measure
restricted to `[0,1]`. This specifies the paper's unadorned `L_p`. -/
abbrev IntervalLp (p : FiniteBanachExponent) :=
  MeasureTheory.Lp 𝕜 p.val (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

/-- Corollary 1.2 (`cor:ellp-Lp`): the two mixed continuous-function spaces
are primary for every finite exponent at least one. -/
def MixedSpacePrimariness : Prop :=
  ∀ p : FiniteBanachExponent,
    IsPrimary 𝕜 C(UnitInterval, ScalarEllp 𝕜 p) ∧
      IsPrimary 𝕜 C(UnitInterval, IntervalLp 𝕜 p)

/-- The UPFP assertion used inside the proof of Corollary 1.2.
This is kept separate from primariness: no general implication from UPFP to
primariness is built into any definition. -/
def MixedSpaceUPFP : Prop :=
  ∀ p : FiniteBanachExponent,
    HasUPFP 𝕜 C(UnitInterval, ScalarEllp 𝕜 p) ∧
      HasUPFP 𝕜 C(UnitInterval, IntervalLp 𝕜 p)

end CKEUPFP
