import JFA.MrowkaCountableSplit
import JFA.CountableCZeroRetracts
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
variable {D : Type} [TopologicalSpace D] [DiscreteTopology D]
variable (S : Set 𝒜) [Countable S]
local instance selectedTopology : TopologicalSpace S := ⊥
local instance selectedDiscrete : DiscreteTopology S := ⟨rfl⟩
variable (h𝒜 : JFA.IsAlmostDisjoint 𝒜)

theorem supportJoin_mem (x : C₀(D × ℕ, 𝕜) × C₀(D × S, 𝕜)) :
    JFA.mrowkaSupportJoin S h𝒜 x ∈ JFA.mrowkaSupportedSubmodule S := by
  intro d A hA
  change JFA.mrowkaNaturalLift h𝒜 x.1 (d, Sum.inr A) +
    JFA.mrowkaFamilyLift S h𝒜 x.2 (d, Sum.inr A) = 0
  rw [JFA.mrowkaNaturalLift_inr, JFA.mrowkaFamilyLift_outside S h𝒜 _ d A hA, add_zero]

def supportedJoin : (C₀(D × ℕ, 𝕜) × C₀(D × S, 𝕜)) →L[𝕜]
    JFA.mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S :=
  (JFA.mrowkaSupportJoin S h𝒜).codRestrict _ (supportJoin_mem S h𝒜)

theorem supportedJoin_injective : Function.Injective (supportedJoin (𝕜 := 𝕜) (D := D) S h𝒜) := by
  intro x y h
  have hv : JFA.mrowkaSupportJoin S h𝒜 x = JFA.mrowkaSupportJoin S h𝒜 y :=
    congrArg Subtype.val h
  have hsecond : x.2 = y.2 := by
    ext q
    have he := congrArg (fun f : C₀(D × JFA.Mrowka 𝒜, 𝕜) => f (q.1, Sum.inr q.2.val)) hv
    change JFA.mrowkaNaturalLift h𝒜 x.1 _ + JFA.mrowkaFamilyLift S h𝒜 x.2 _ =
      JFA.mrowkaNaturalLift h𝒜 y.1 _ + JFA.mrowkaFamilyLift S h𝒜 y.2 _ at he
    simpa only [JFA.mrowkaNaturalLift_inr, JFA.mrowkaFamilyLift_selected, zero_add] using he
  refine Prod.ext ?_ hsecond
  ext q
  have he := congrArg (fun f : C₀(D × JFA.Mrowka 𝒜, 𝕜) => f (q.1, Sum.inl q.2)) hv
  change JFA.mrowkaNaturalLift h𝒜 x.1 _ + JFA.mrowkaFamilyLift S h𝒜 x.2 _ =
    JFA.mrowkaNaturalLift h𝒜 y.1 _ + JFA.mrowkaFamilyLift S h𝒜 y.2 _ at he
  simpa only [JFA.mrowkaNaturalLift_inl, hsecond, add_left_inj] using he

theorem supportedJoin_surjective : Function.Surjective (supportedJoin (𝕜 := 𝕜) (D := D) S h𝒜) := by
  intro f
  refine ⟨JFA.mrowkaSupportSplit S h𝒜 f, Subtype.ext ?_⟩
  exact congrArg (fun T => T f) (JFA.mrowkaSupportJoin_split (𝕜 := 𝕜) (D := D) S h𝒜)

/-- Disjoint-tail coordinates give a bounded isomorphism onto the full supported subspace. -/
def countableSupportEquiv : JFA.mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S ≃L[𝕜]
    (C₀(D × ℕ, 𝕜) × C₀(D × S, 𝕜)) := by
  letI : CompleteSpace (JFA.mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S) :=
    (JFA.mrowkaSupportedSubmodule_isClosed (𝕜 := 𝕜) (D := D) S).completeSpace_coe
  exact (ContinuousLinearEquiv.ofBijective (supportedJoin S h𝒜)
    (LinearMap.ker_eq_bot.mpr (supportedJoin_injective S h𝒜))
    (LinearMap.range_eq_top.mpr (supportedJoin_surjective S h𝒜))).symm

end Posets
