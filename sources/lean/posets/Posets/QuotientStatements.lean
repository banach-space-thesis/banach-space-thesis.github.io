import Posets.SupportingStatements
import PosetsCommon.CZeroSum
import Mathlib.Order.WithBot
import Mathlib.Analysis.Normed.Module.Basic

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon Filter Topology
open scoped ZeroAtInfty
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

/-- Definition 6.13, adjoining two genuinely new extremal elements. -/
abbrev BoundedExtension (P : Type*) := WithBot (WithTop P)
def middle {P : Type*} (p : P) : BoundedExtension P := ((p : WithTop P) : WithBot (WithTop P))

/-- A common nonseparable subspace is represented by isometric inclusions
which agree with every order embedding. Z need not be complete. -/
def CommonSubspace {P : Type*} [PartialOrder P] (X : P → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    (ι : ∀ s t, X s →L[𝕜] X t) : Prop :=
  ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace 𝕜 Z),
    ¬ TopologicalSpace.SeparableSpace Z ∧ ∃ j : ∀ t, Z →ₗᵢ[𝕜] X t,
      ∀ s t, s ≤ t → ∀ z, ι s t (j s z) = j t z

/-- Proposition 6.6, preserving the common-Z hypothesis in the FINAL zip.
An existential subalgebra with this exact carrier bundles the literal incidence
operators; no closure or multiplication theorem is silently assumed. -/
def Proposition_6_6_printed (P : Type) [Fintype P] [PartialOrder P]
    (X : P → Type) [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] (ι : ∀ s t, X s →L[𝕜] X t) : Prop :=
  FewOperators 𝕜 X ι → CommonSubspace 𝕜 X ι →
  ∃ C : Subalgebra 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜)),
    (C : Set _) = oppositeFiniteIncidenceOperators 𝕜 P ∧
    ∃ θ : BoundedHom 𝕜 ((∀ p, X p) →L[𝕜] (∀ p, X p)) C,
    ∃ ρ : BoundedHom 𝕜 C ((∀ p, X p) →L[𝕜] (∀ p, X p)),
      StrongSplit 𝕜 (∀ p, X p) C θ ρ ∧ Isometry ρ ∧ ‖θ.toContinuousLinearMap‖ = 1

/-- The standard nonempty-poset convention is explicit for the norm-one clause,
as agreed with the author on 1 October 2026. -/
def Proposition_6_6 (P : Type) [Fintype P] [PartialOrder P] [Nonempty P]
    (X : P → Type) [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] (ι : ∀ s t, X s →L[𝕜] X t) : Prop :=
  Proposition_6_6_printed 𝕜 P X ι

/-- Submultiplicative algebra norm without completeness or agreement with a
pre-existing topology; this is the meaning of normable in Proposition 6.8. -/
def AlgebraNormExists (A : Type*) [Ring A] [Module 𝕜 A] : Prop :=
  ∃ n : A → ℝ, (∀ x, 0 ≤ n x) ∧ (∀ x, n x = 0 ↔ x = 0) ∧
    (∀ x y, n (x + y) ≤ n x + n y) ∧
    (∀ a : 𝕜, ∀ x, n (a • x) = ‖a‖ * n x) ∧
    ∀ x y, n (x * y) ≤ n x * n y

def Proposition_6_8 (P : Type) [PartialOrder P] [LocallyFiniteOrder P] : Prop :=
  AlgebraNormExists 𝕜 (IncidenceAlgebra 𝕜 P) ↔ Finite P

/-- Proposition 6.11. Closedness and all subalgebra operations are asserted for
exactly the matrix zero pattern, rather than built into an unchecked instance. -/
def Proposition_6_11 (P : Type) [PartialOrder P] [Countable P] [Infinite P] : Prop :=
  ∃ C : Subalgebra 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P),
    (C : Set _) = incidenceOperators 𝕜 P ∧
      IsClosed (C : Set (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P))

def BoundedRowsOn {P : Type*} (M : P → P → 𝕜) : Prop :=
  (∀ s, Summable (fun t => ‖M s t‖)) ∧ ∃ C : ℝ, ∀ s, (∑' t, ‖M s t‖) ≤ C

def ZeroColumnsOn {P : Type*} (M : P → P → 𝕜) : Prop :=
  ∀ t, Tendsto (fun s => M s t) cofinite (𝓝 0)

/-- Proposition 6.15(a,b), with both necessary conditions, exact norm, and
existence in the converse. Summability is explicit to avoid totalised-tsum errors. -/
def Proposition_6_15 (P : Type) [Countable P] [Infinite P] : Prop :=
  (∀ T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P,
    BoundedRowsOn 𝕜 (scalarMatrix 𝕜 T) ∧ ZeroColumnsOn 𝕜 (scalarMatrix 𝕜 T) ∧
    ‖T‖ = ⨆ s, ∑' t, ‖scalarMatrix 𝕜 T s t‖) ∧
  (∀ M : P → P → 𝕜, BoundedRowsOn 𝕜 M → ZeroColumnsOn 𝕜 M →
    ∃ T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P, scalarMatrix 𝕜 T = M)

/-- Proposition 6.22. Uses the concrete c₀ sum and the opposite-order matrix
algebra; the extra bottom and top spaces are retained as hypotheses. -/
def Proposition_6_22 (P : Type) [PartialOrder P] [Countable P]
    (X : BoundedExtension P → Type)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] (ι : ∀ s t, X s →L[𝕜] X t) : Prop :=
  FewOperators 𝕜 X ι →
  let Y := DependentCZeroSum 𝕜 (fun p : P => X (middle p))
  ∃ C : Subalgebra 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P),
    (C : Set _) = oppositeIncidenceOperators 𝕜 P ∧
    ∃ θ : BoundedHom 𝕜 (Y →L[𝕜] Y) C,
    ∃ ρ : BoundedHom 𝕜 C (Y →L[𝕜] Y), StrongSplit 𝕜 Y C θ ρ

end Posets
