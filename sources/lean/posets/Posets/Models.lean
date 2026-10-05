import Posets.Definitions
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.SetTheory.Cardinal.Continuum

noncomputable section
open scoped ZeroAtInfty ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.typeDecidableEq
open Filter Topology ThesisCommon
namespace Posets

/-- A type copy with the discrete topology, independent of any topology on P. -/
structure Discrete (P : Type*) where
  val : P
instance (P : Type*) : TopologicalSpace (Discrete P) := ⊥
instance (P : Type*) : DiscreteTopology (Discrete P) := ⟨rfl⟩

abbrev CZeroOn (𝕜 P : Type*) [RCLike 𝕜] := C₀(Discrete P, 𝕜)

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The coordinate vector e_t in c₀(P), with the literal discrete C₀ topology. -/
def unitVector {P : Type*} (t : P) : CZeroOn 𝕜 P where
  toFun s := if s.val = t then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(isCompact_singleton (x := (⟨t⟩ : Discrete P))).compl_mem_cocompact] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
    have hst : s.val ≠ t := by
      intro h
      apply hs
      cases s
      cases h
      rfl
    simp [hst]

/-- Row s, column t, as in Definition 6.9; the order is s ≤ t. -/
def scalarMatrix {P : Type*} (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) (s t : P) : 𝕜 :=
  T (unitVector 𝕜 t) ⟨s⟩

def incidenceOperators (P : Type*) [PartialOrder P] :
    Set (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) :=
  {T | ∀ s t, ¬ s ≤ t → scalarMatrix 𝕜 T s t = 0}

/-- Finite incidence algebras represented as actual operators on ℓ∞(P).
This fixes the norm without imposing the entrywise maximum matrix norm. -/
def finiteIncidenceOperators (P : Type*) [Fintype P] [PartialOrder P] :
    Set ((P → 𝕜) →L[𝕜] (P → 𝕜)) :=
  {T | ∀ s t, ¬ s ≤ t → T (Pi.single t 1) s = 0}

/-- Opposite order, written on the ORIGINAL index type to avoid changing the
underlying normed-space instances via an order-dual type synonym. -/
def oppositeIncidenceOperators (P : Type*) [PartialOrder P] :
    Set (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) :=
  {T | ∀ s t, ¬ t ≤ s → scalarMatrix 𝕜 T s t = 0}

def oppositeFiniteIncidenceOperators (P : Type*) [Fintype P] [PartialOrder P] :
    Set ((P → 𝕜) →L[𝕜] (P → 𝕜)) :=
  {T | ∀ s t, ¬ t ≤ s → T (Pi.single t 1) s = 0}

/-- An isometric multiplicative identification with a specified concrete operator
algebra. The range equation is essential: embedding alone would be too weak. -/
def RepresentedBy (C E : Type*) [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (S : Set (E →L[𝕜] E)) : Prop :=
  ∃ f : BoundedHom 𝕜 C (E →L[𝕜] E), Isometry f ∧ Set.range f = S

/-- The five building blocks of 𝔄, up to isometric algebra isomorphism.
Positive matrix size is encoded by n+1. Empty finite/countable posets are allowed. -/
def AdmissibleAlgebra (C : Type) [NormedRing C] [NormedAlgebra 𝕜 C] : Prop :=
  Subsingleton C ∨
  (∃ n : ℕ, RepresentedBy 𝕜 C (Fin (n + 1) → 𝕜) Set.univ) ∨
  (∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P),
    RepresentedBy 𝕜 C (P → 𝕜) (finiteIncidenceOperators 𝕜 P)) ∨
  (∃ (P : Type) (_ : Countable P) (_ : PartialOrder P),
    RepresentedBy 𝕜 C (CZeroOn 𝕜 P) (incidenceOperators 𝕜 P)) ∨
  RepresentedBy 𝕜 C (cZero 𝕜) Set.univ

/-- The actual uniformly bounded product, with the supremum norm and pointwise
multiplication, supplied by mathlib's dependent ℓ∞ space. -/
abbrev NormedProduct (C : ℕ → Type*) [∀ n, NormedAddCommGroup (C n)] := lp C ∞

section Quotient
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance separableRange_closed :
    IsClosed (JFA.separableRangeSubmodule (𝕜 := 𝕜) (E := E) (F := E) : Set (E →L[𝕜] E)) :=
  JFA.isClosed_separableOperators

/-- The genuine normed quotient by the separable-range submodule. -/
abbrev SeparableQuotient :=
  (E →L[𝕜] E) ⧸ JFA.separableRangeSubmodule (𝕜 := 𝕜) (E := E) (F := E)

abbrev quotientMap : (E →L[𝕜] E) →ₗ[𝕜] SeparableQuotient 𝕜 E :=
  (JFA.separableRangeSubmodule (𝕜 := 𝕜) (E := E) (F := E)).mkQ

/-- Multiplication in the quotient is expressed on representatives. This avoids
adding a second, potentially incompatible quotient-ring structure. -/
def IsQuotientClosedIdeal (I : Set (SeparableQuotient 𝕜 E)) : Prop :=
  IsClosed I ∧ (0 : SeparableQuotient 𝕜 E) ∈ I ∧
  (∀ a ∈ I, ∀ b ∈ I, a + b ∈ I) ∧
  (∀ c : 𝕜, ∀ a ∈ I, c • a ∈ I) ∧
  (∀ A T : E →L[𝕜] E, quotientMap 𝕜 E T ∈ I →
    quotientMap 𝕜 E (A * T) ∈ I ∧ quotientMap 𝕜 E (T * A) ∈ I)

def QuotientClosedIdeals := {I : Set (SeparableQuotient 𝕜 E) // IsQuotientClosedIdeal 𝕜 E I}
instance : PartialOrder (QuotientClosedIdeals 𝕜 E) := inferInstanceAs (PartialOrder (Subtype _))

def IdealsAboveCompact :=
  {I : Set (E →L[𝕜] E) // IsClosedIdeal 𝕜 I ∧ {T : E →L[𝕜] E | IsCompactOperator T} ⊂ I}
instance : PartialOrder (IdealsAboveCompact 𝕜 E) := inferInstanceAs (PartialOrder (Subtype _))
end Quotient

/-- Multiplicative linear maps are used here because continuity is a conclusion
or is explicitly denied. No continuity is hidden in this definition. -/
def IsMultiplicative {A B : Type*} [AddCommMonoid A] [Module 𝕜 A] [Mul A]
    [AddCommMonoid B] [Module 𝕜 B] [Mul B] (f : A →ₗ[𝕜] B) : Prop :=
  ∀ a b, f (a * b) = f a * f b

/-- T₂ as its literal subset in the finite-dimensional 2×2 matrix algebra. -/
def triangularTwo : Set (Matrix (Fin 2) (Fin 2) 𝕜) := {M | M 1 0 = 0}

end Posets
