import JFA.MrowkaCountableSplit
import JFA.CountableCZeroRetracts
import JFA.MrowkaSupport
import JFA.CompactIdeal

/-! Separable ranges have countable family support. The explicit splitting of
that support, followed by a numbering of the two discrete coordinate sets,
gives a literal factorisation through scalar c₀. A compact operator has a
compact first factor, because its range lies in a closed supported subspace. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Set
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
variable {D : Type*} [TopologicalSpace D] [DiscreteTopology D] [Countable D]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem separable_mrowka_factors_cZero (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : E →L[𝕜] C₀(D × Mrowka 𝒜, 𝕜))
    (hT : HasSeparableRange 𝕜 E C₀(D × Mrowka 𝒜, 𝕜) T) :
    ∃ A : E →L[𝕜] cZero 𝕜, ∃ B : cZero 𝕜 →L[𝕜] C₀(D × Mrowka 𝒜, 𝕜),
      T = B.comp A ∧ (IsCompactOperator T → IsCompactOperator A) := by
  let S := mrowkaSetSupport (Set.range T)
  have hS : S.Countable := mrowka_set_support_countable hT
  letI : Countable S := hS.to_subtype
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  have hTS : ∀ x, T x ∈ mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S := by
    intro x d A hA
    by_contra hval
    exact hA ⟨T x, ⟨x, rfl⟩, d, hval⟩
  let T' := T.codRestrict (mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S) hTS
  let split := mrowkaSupportSplit (𝕜 := 𝕜) (D := D) S h𝒜
  let join := mrowkaSupportJoin (𝕜 := 𝕜) (D := D) S h𝒜
  obtain ⟨C, V, hVC⟩ := exists_countable_czero_product_retract (𝕜 := 𝕜)
    (ι := D × ℕ) (κ := D × S)
  refine ⟨C.comp (split.comp T'), join.comp V, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    change T x = join (V (C (split (T' x))))
    have h1 : V (C (split (T' x))) = split (T' x) :=
      congrArg (fun L => L (split (T' x))) hVC
    rw [h1]
    have h2 := congrArg (fun L => L (T' x))
      (mrowkaSupportJoin_split (𝕜 := 𝕜) (D := D) S h𝒜)
    exact h2.symm
  · intro hc
    have hc' : IsCompactOperator T' :=
      hc.codRestrict hTS (mrowkaSupportedSubmodule_isClosed (𝕜 := 𝕜) (D := D) S)
    exact (hc'.clm_comp split).clm_comp C

theorem amplified_separable_factors_cZero (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)
    (hT : HasSeparableRange 𝕜 (AmplifiedMrowka 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜) T) :
    ∃ A : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] cZero 𝕜,
    ∃ B : cZero 𝕜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜,
      T = B.comp A ∧ (IsCompactOperator T → IsCompactOperator A) :=
  separable_mrowka_factors_cZero (D := ℕ) h𝒜 T hT

theorem amplified_factorizationOperators_eq_separableOperators (h𝒜 : IsAlmostDisjoint 𝒜) :
    factorizationOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) (cZero 𝕜) =
      separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) := by
  letI : SeparableSpace (cZero 𝕜) := czero_countable_discrete_separable
  apply subset_antisymm factorizationOperators_subset_separableOperators
  intro T hT
  obtain ⟨A, B, hAB, _⟩ := amplified_separable_factors_cZero h𝒜 T hT
  exact Submodule.subset_span ⟨A, B, hAB⟩

theorem amplified_cZeroFactorizations_closedIdeal (h𝒜 : IsAlmostDisjoint 𝒜) :
    IsClosedOperatorIdeal 𝕜 (AmplifiedMrowka 𝕜 𝒜)
      (factorizationOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) (cZero 𝕜)) := by
  rw [amplified_factorizationOperators_eq_separableOperators h𝒜]
  exact separableOperators_closedIdeal

end JFA
