import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Order.Compact

/-!
Definitions for the statements of Antonio Acuaviva,
"Factorizations and minimality of the Calkin Algebra norm for C(K)-spaces",
J. London Math. Soc. 112 (2025), e70321, DOI: 10.1112/jlms.70321.

This file supplies definitions for the statements and proof modules.
All mathematical notions below are defined;
none is introduced as an axiom or an unspecified predicate.

The Calkin space is the actual quotient by the submodule of compact operators.
Submultiplicativity of a norm on it is expressed on representatives, using
[S][T] = [S.comp T]. This avoids needing a separate quotient-ring instance.
The norms themselves are functions on quotient classes, not on representatives.

Section 3 of the paper has an author-confirmed reversed inequality in its explanation
of vanishing at infinity. We use mathlib's standard C₀: for every ε > 0,
{k | ε ≤ ‖f k‖} is compact. The paper prints {k | ‖f k‖ ≤ ε}.
-/

noncomputable section

open Filter Topology
open scoped ZeroAtInfty

namespace JLMS

universe u v w

/-- Every nonempty subset has an isolated point in its relative topology. -/
def IsScattered (K : Type u) [TopologicalSpace K] : Prop :=
  ∀ s : Set K, s.Nonempty →
    ∃ x ∈ s, ∃ U : Set K, IsOpen U ∧ s ∩ U = {x}

/-- Continuous scalar-valued functions vanishing at infinity, with sup norm. -/
abbrev CZero (𝕜 : Type*) [RCLike 𝕜] (K : Type*) [TopologicalSpace K] :=
  C₀(K, 𝕜)

/-- The usual sequence space c₀; ℕ carries its standard discrete topology. -/
abbrev cZero (𝕜 : Type*) [RCLike 𝕜] := C₀(ℕ, 𝕜)

/-- The usual ℓ¹ over the same scalar field as all other spaces. -/
abbrev ellOne (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ℕ => 𝕜) 1

section Operators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Distance, in operator norm, to all compact operators E → F. -/
def essentialNorm (T : E →L[𝕜] F) : ℝ :=
  sInf {r : ℝ | ∃ S : E →L[𝕜] F, IsCompactOperator S ∧ r = ‖T - S‖}

/-- The Banach adjoint T*: F* → E*, with T*(φ)(x) = φ(T x).
This is linear over 𝕜, including for complex scalars. -/
def banachAdjoint (T : E →L[𝕜] F) : (F →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T

@[simp] theorem banachAdjoint_apply (T : E →L[𝕜] F) (φ : F →L[𝕜] 𝕜) (x : E) :
    banachAdjoint T φ x = φ (T x) := rfl

/-- The essential norm of the Banach adjoint, using ALL compact maps F* → E*. -/
def dualEssentialNorm (T : E →L[𝕜] F) : ℝ :=
  essentialNorm (𝕜 := 𝕜) (E := F →L[𝕜] 𝕜) (F := E →L[𝕜] 𝕜)
    (banachAdjoint T)

end Operators

section CodomainHypotheses

variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- An isomorphic copy of ℓ¹, not necessarily an isometric copy.
The lower bound makes the bounded linear embedding an isomorphism onto its range. -/
def ContainsEllOne : Prop :=
  ∃ J : ellOne 𝕜 →L[𝕜] X, ∃ c : ℝ, 0 < c ∧
    ∀ x : ellOne 𝕜, c * ‖x‖ ≤ ‖J x‖

/-- Sequential compactness of the CLOSED dual unit ball in the weak* topology.
Weak* convergence is spelled out as convergence at each x ∈ X; the subsequence
is common to all x, not chosen separately for each x. -/
def DualBallWeakStarSeqCompact : Prop :=
  ∀ f : ℕ → (X →L[𝕜] 𝕜), (∀ n, ‖f n‖ ≤ 1) →
    ∃ φ : X →L[𝕜] 𝕜, ‖φ‖ ≤ 1 ∧
      ∃ s : ℕ → ℕ, StrictMono s ∧
        ∀ x : X, Tendsto (fun n => f (s n) x) atTop (𝓝 (φ x))

/-- The disjunction in Theorems 1.6 and 1.7, with no additional restriction on X. -/
def AdmissibleCodomain : Prop :=
  (¬ ContainsEllOne 𝕜 X) ∨ DualBallWeakStarSeqCompact 𝕜 X

end CodomainHypotheses

section Norms

variable (𝕜 : Type*) [RCLike 𝕜]
variable {A : Type*} [AddCommGroup A] [Module 𝕜 A]

/-- An arbitrary vector norm; there is no preassigned topology on A here. -/
def IsVectorNorm (n : A → ℝ) : Prop :=
  (∀ x, 0 ≤ n x) ∧
  (∀ x, n x = 0 ↔ x = 0) ∧
  (∀ x y, n (x + y) ≤ n x + n y) ∧
  (∀ a : 𝕜, ∀ x, n (a • x) = ‖a‖ * n x)

/-- The paper's algebra norm: a submultiplicative vector norm.
Neither completeness, continuity, nor n(1) = 1 is required. -/
def IsAlgebraNorm {B : Type*} [NonUnitalRing B] [Module 𝕜 B] (n : B → ℝ) : Prop :=
  IsVectorNorm 𝕜 n ∧ ∀ x y, n (x * y) ≤ n x * n y

/-- Equivalence of norms, rather than literal equality of their values. -/
def EquivalentNorms {B : Type*} (n m : B → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ x, c * n x ≤ m x ∧ m x ≤ C * n x

/-- Completeness for the metric induced by n, written in epsilon-N form.
In particular this does not use the pre-existing topology of any other norm. -/
def CompleteNorm {B : Type*} [AddCommGroup B] (n : B → ℝ) : Prop :=
  ∀ x : ℕ → B,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ i j : ℕ, N ≤ i → N ≤ j → n (x i - x j) < ε) →
    ∃ y : B, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ i : ℕ, N ≤ i → n (x i - y) < ε

/-- Any two algebra norms are equivalent, exactly as defined in Section 1.1. -/
def HasUniqueAlgebraNorm {B : Type*} [NonUnitalRing B] [Module 𝕜 B] : Prop :=
  ∀ n m : B → ℝ, IsAlgebraNorm 𝕜 n → IsAlgebraNorm 𝕜 m → EquivalentNorms n m

end Norms

section Calkin

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- B(E)/K(E), as an actual quotient vector space. -/
abbrev Calkin := (E →L[𝕜] E) ⧸ compactOperator (RingHom.id 𝕜) E E

/-- The quotient map T ↦ [T]. -/
def calkinMk (T : E →L[𝕜] E) : Calkin 𝕜 E := Submodule.Quotient.mk T

/-- A vector norm on quotient classes, submultiplicative for [S][T] = [ST].
The representative formulation imposes the usual algebra-norm condition because
the quotient map is surjective and compact operators form a two-sided ideal. -/
def IsCalkinAlgebraNorm (n : Calkin 𝕜 E → ℝ) : Prop :=
  IsVectorNorm 𝕜 n ∧
    ∀ S T : E →L[𝕜] E,
      n (calkinMk 𝕜 E (S.comp T)) ≤ n (calkinMk 𝕜 E S) * n (calkinMk 𝕜 E T)

/-- For every competing norm, one positive lower-comparison constant works for
ALL operators. That constant may depend on the competing norm. -/
def EssentialNormIsMinimal : Prop :=
  ∀ n : Calkin 𝕜 E → ℝ, IsCalkinAlgebraNorm 𝕜 E n →
    ∃ c : ℝ, 0 < c ∧
      ∀ T : E →L[𝕜] E, c * essentialNorm T ≤ n (calkinMk 𝕜 E T)

/-- Any two complete algebra norms on the Calkin algebra are equivalent. -/
def HasUniqueCompleteCalkinNorm : Prop :=
  ∀ n m : Calkin 𝕜 E → ℝ,
    IsCalkinAlgebraNorm 𝕜 E n → IsCalkinAlgebraNorm 𝕜 E m →
    CompleteNorm n → CompleteNorm m → EquivalentNorms n m

/-- Any two algebra norms on the Calkin algebra are equivalent. -/
def HasUniqueCalkinNorm : Prop :=
  ∀ n m : Calkin 𝕜 E → ℝ,
    IsCalkinAlgebraNorm 𝕜 E n → IsCalkinAlgebraNorm 𝕜 E m → EquivalentNorms n m

/-- Every algebra norm dominated by the dual essential norm equals it pointwise.
The conclusion is equality, not just equivalence. -/
def DualEssentialNormHasBonsallMinimality : Prop :=
  ∀ n : Calkin 𝕜 E → ℝ, IsCalkinAlgebraNorm 𝕜 E n →
    (∀ T : E →L[𝕜] E, n (calkinMk 𝕜 E T) ≤ dualEssentialNorm T) →
    ∀ T : E →L[𝕜] E, n (calkinMk 𝕜 E T) = dualEssentialNorm T

end Calkin

/-- The closed ordinal interval [0, α], with the inherited order topology.
The universe is arbitrary: α is not restricted to countable ordinals. -/
abbrev OrdinalInterval (α : Ordinal.{u}) := Set.Icc (0 : Ordinal.{u}) α

/-- Continuous functions on the compact ordinal interval, with the sup norm. -/
abbrev OrdinalC (𝕜 : Type*) [RCLike 𝕜] (α : Ordinal.{u}) :=
  C(OrdinalInterval α, 𝕜)

end JLMS
