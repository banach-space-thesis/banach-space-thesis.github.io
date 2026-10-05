import PosetsCommon.Algebra
import JFA.SeparableIdeal
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.DerivedSet

/-! Vocabulary from Sections 1, 2, 4 and 6 of the final uploaded source.
The Mrówka topology and separable-range ideal are imported from JFA, not copied.
All operators are continuous linear maps over ℝ or ℂ. -/
noncomputable section
open scoped ZeroAtInfty
open ThesisCommon
namespace Posets

abbrev IsAlmostDisjoint := JFA.IsAlmostDisjoint
abbrev Mrowka := JFA.Mrowka
abbrev Space (𝕜 : Type*) [RCLike 𝕜] (𝒜 : Set (Set ℕ)) := JFA.MrowkaCZero 𝕜 𝒜
abbrev cZero (𝕜 : Type*) [RCLike 𝕜] := JFA.cZero 𝕜
abbrev HasSeparableRange := JFA.HasSeparableRange

variable (𝕜 : Type*) [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Literal factorisation through c₀, stronger than a formal ideal-span membership. -/
def FactorsThroughCZero (T : E →L[𝕜] F) : Prop :=
  ∃ A : E →L[𝕜] cZero 𝕜, ∃ B : cZero 𝕜 →L[𝕜] F, T = B.comp A

/-- Definition 6.1: the actual operator conditions relative to a given family
of embeddings. Off-order embeddings are zero, as specified in the following remark. -/
def FewOperators {P : Type*} [PartialOrder P] (X : P → Type*)
    [∀ t, NormedAddCommGroup (X t)] [∀ t, NormedSpace 𝕜 (X t)]
    (ι : ∀ s t, X s →L[𝕜] X t) : Prop :=
  (∀ t, ¬ TopologicalSpace.SeparableSpace (X t)) ∧
  (∀ s t, s ≤ t → Isometry (ι s t)) ∧
  (∀ r s t, r ≤ s → s ≤ t → (ι s t).comp (ι r s) = ι r t) ∧
  (∀ s t, ¬ s ≤ t → ι s t = 0) ∧
  (∀ s t, s ≤ t → ∀ T : X s →L[𝕜] X t,
    ∃ a : 𝕜, ∃ S : X s →L[𝕜] X t,
      HasSeparableRange 𝕜 (X s) (X t) S ∧ T = a • ι s t + S) ∧
  (∀ s t, ¬ s ≤ t → ∀ T : X s →L[𝕜] X t,
    HasSeparableRange 𝕜 (X s) (X t) T)

/-- s(f), regarded as a subset of the family rather than of all subsets of ℕ. -/
def familySupport {𝒜 : Set (Set ℕ)} (f : Space 𝕜 𝒜) : Set 𝒜 :=
  {A | f (Sum.inr A) ≠ 0}

def familySupportSet {𝒜 : Set (Set ℕ)} (X : Set (Space 𝕜 𝒜)) : Set 𝒜 :=
  {A | ∃ f ∈ X, f (Sum.inr A) ≠ 0}

/-- Section 3: I_Y does not factor through T. -/
def DoesNotFactorIdentity (T : E →L[𝕜] E) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] : Prop :=
  ¬ ∃ A : F →L[𝕜] E, ∃ B : E →L[𝕜] F,
    B.comp (T.comp A) = ContinuousLinearMap.id 𝕜 F

/-- Sections 2 and 1: strong splitting with precisely the separable-range kernel.
The final theorem adds isometry and the exact norm of θ separately. -/
def StrongSplit (E C : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
    (θ : BoundedHom 𝕜 (E →L[𝕜] E) C)
    (ρ : BoundedHom 𝕜 C (E →L[𝕜] E)) : Prop :=
  Function.Surjective θ ∧
  (∀ T, θ T = 0 ↔ HasSeparableRange 𝕜 E E T) ∧
  Function.RightInverse ρ θ

end Posets
