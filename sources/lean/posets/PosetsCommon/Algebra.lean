import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! Reusable vocabulary for possibly nonunital Banach algebra homomorphisms
and closed two-sided linear ideals. No existence result is a structure field. -/
noncomputable section
namespace ThesisCommon

variable (𝕜 : Type*) [RCLike 𝕜]

/-- A bounded linear map that preserves products. No preservation of a unit
is required: the paper's right inverses can take values in a proper corner. -/
structure BoundedHom (A B : Type*) [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [Mul A] [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Mul B] extends A →L[𝕜] B where
  map_mul' : ∀ a b, toContinuousLinearMap (a * b) =
    toContinuousLinearMap a * toContinuousLinearMap b

variable {𝕜}
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Mul B]

instance : CoeFun (BoundedHom 𝕜 A B) (fun _ => A → B) :=
  ⟨fun f => f.toContinuousLinearMap⟩

theorem BoundedHom.continuous (f : BoundedHom 𝕜 A B) : Continuous f :=
  f.toContinuousLinearMap.continuous

variable (𝕜)

/-- Closed, scalar-linear, two-sided ideal, encoded in the original norm topology. -/
def IsClosedIdeal (I : Set A) : Prop :=
  IsClosed I ∧ (0 : A) ∈ I ∧
  (∀ a ∈ I, ∀ b ∈ I, a + b ∈ I) ∧
  (∀ c : 𝕜, ∀ a ∈ I, c • a ∈ I) ∧
  (∀ a : A, ∀ b ∈ I, a * b ∈ I ∧ b * a ∈ I)

def ClosedIdeal (A : Type*) [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A] :=
  {I : Set A // IsClosedIdeal 𝕜 I}

instance : PartialOrder (ClosedIdeal 𝕜 A) := inferInstanceAs (PartialOrder (Subtype _))

def IsMaximalClosedIdeal (I : Set A) : Prop :=
  IsClosedIdeal 𝕜 I ∧ I ≠ Set.univ ∧
  ∀ J : Set A, IsClosedIdeal 𝕜 J → I ⊆ J → J = I ∨ J = Set.univ

def HasUniqueMaximalClosedIdeal (A : Type*) [NormedAddCommGroup A]
    [NormedSpace 𝕜 A] [Mul A] : Prop := ∃! I : Set A, IsMaximalClosedIdeal 𝕜 I

def NontrivialClosedIdeals (A : Type*) [NormedAddCommGroup A]
    [NormedSpace 𝕜 A] [Mul A] :=
  {I : Set A // IsClosedIdeal 𝕜 I ∧ I ≠ {0} ∧ I ≠ Set.univ}

def MaximalClosedIdeals (A : Type*) [NormedAddCommGroup A]
    [NormedSpace 𝕜 A] [Mul A] := {I : Set A // IsMaximalClosedIdeal 𝕜 I}

/-- An actual isometric algebra isomorphism, described by a linear isometry
equivalence plus multiplicativity. -/
def IsometricallyIsomorphic (A B : Type*) [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [Mul A] [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Mul B] : Prop :=
  ∃ e : A ≃ₗᵢ[𝕜] B, ∀ a b, e (a * b) = e a * e b

/-- The zero algebra has no proper maximal closed ideal. -/
theorem no_maximalClosedIdeal_of_subsingleton [Subsingleton A] (I : Set A) :
    ¬ IsMaximalClosedIdeal 𝕜 I := by
  rintro ⟨hI, hproper, _⟩
  apply hproper
  apply Set.eq_univ_of_forall
  intro a
  simpa only [Subsingleton.elim a 0] using hI.2.1

theorem not_uniqueMaximal_of_subsingleton [Subsingleton A] :
    ¬ HasUniqueMaximalClosedIdeal 𝕜 A := by
  rintro ⟨I, hI, _⟩
  exact no_maximalClosedIdeal_of_subsingleton 𝕜 I hI

end ThesisCommon
