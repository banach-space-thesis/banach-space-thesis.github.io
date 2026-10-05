import Posets.OperatorExceptionalSet
import Posets.GeneratorDensity
import Posets.FamilySupportConverse
import Posets.SeparableRangeFactorization

/-! Lemma 4.18: reduced-matrix agreement, non-rejection, and factorisation
through c₀ under admission outside countable exceptional families. -/

noncomputable section
open Filter Topology
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 ℬ : Set (Set ℕ)}

/-- It suffices to control family-point values on the indicator generators. -/
theorem factorsThroughCZero_of_generator_support
    (h𝒜 : IsAlmostDisjoint 𝒜) (hℬ : IsAlmostDisjoint ℬ)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (C : Set 𝒜) (D : Set ℬ)
    (hC : C.Countable) (hD : D.Countable)
    (hz : ∀ A ∉ C, ∀ B ∉ D, T (familyVector 𝕜 𝒜 h𝒜 A) (Sum.inr B) = 0) :
    FactorsThroughCZero 𝕜 T := by
  classical
  letI : Countable C := hC.to_subtype
  let Q : Set ℬ := D ∪ ((⋃ n : ℕ, familySupport 𝕜 (T (isolatedVector 𝕜 𝒜 n))) ∪
    (⋃ A : C, familySupport 𝕜 (T (familyVector 𝕜 𝒜 h𝒜 A.val))))
  have hQ : Q.Countable := hD.union ((Set.countable_iUnion (fun n => familySupport_countable _)).union
    (Set.countable_iUnion (fun A : C => familySupport_countable _)))
  have hzero (B : ℬ) (hB : B ∉ Q) (f : Space 𝕜 𝒜) : T f (Sum.inr B) = 0 := by
    let φ : Space 𝕜 𝒜 →L[𝕜] 𝕜 := (JLMS.evaluation (K := Mrowka ℬ) (Sum.inr B)).comp T
    apply map_eq_zero_of_generators h𝒜 φ
    · intro n
      change T (isolatedVector 𝕜 𝒜 n) (Sum.inr B) = 0
      by_contra hn
      exact hB (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨n, hn⟩)))
    · intro A
      change T (familyVector 𝕜 𝒜 h𝒜 A) (Sum.inr B) = 0
      by_cases hA : A ∈ C
      · by_contra ha
        exact hB (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨⟨A, hA⟩, ha⟩)))
      · exact hz A hA B (fun hb => hB (Or.inl hb))
  let X := LinearMap.range T.toLinearMap
  have hs : (familySupportSet 𝕜 (X : Set (Space 𝕜 ℬ))).Countable := by
    apply hQ.mono
    rintro B ⟨g, ⟨f, rfl⟩, hne⟩
    by_contra hB
    exact hne (hzero B hB f)
  letI : TopologicalSpace.SeparableSpace X := separable_of_familySupportSet_countable hℬ X hs
  apply factorsThroughCZero_of_hasSeparableRange hℬ T
  exact TopologicalSpace.IsSeparable.of_subtype (X : Set (Space 𝕜 ℬ))

theorem factorsThroughCZero_of_admission
    (h𝒜 : IsAlmostDisjoint 𝒜) (hℬ : IsAlmostDisjoint ℬ)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (𝒜' ℬ' : Set (Set ℕ))
    (hAcount : 𝒜'.Countable) (hBcount : ℬ'.Countable)
    (hadmit : Admits 𝕜 (𝒜 \ 𝒜') (ℬ \ ℬ') (reducedMatrix 𝕜 T)) :
    FactorsThroughCZero 𝕜 T := by
  let C : Set 𝒜 := operatorExceptionalFamily h𝒜 T ∪ {A | A.val ∈ 𝒜'}
  let D : Set ℬ := {B | B.val ∈ ℬ'}
  have hC : C.Countable := (operatorExceptionalFamily_countable h𝒜 T).union
    (hAcount.preimage Subtype.val_injective)
  have hD : D.Countable := hBcount.preimage Subtype.val_injective
  apply factorsThroughCZero_of_generator_support h𝒜 hℬ T C D hC hD
  intro A hA B hB
  have hAE : A ∉ operatorExceptionalFamily h𝒜 T := fun h => hA (Or.inl h)
  have hAA : A.val ∉ 𝒜' := fun h => hA (Or.inr h)
  have hBB : B.val ∉ ℬ' := hB
  letI : NeBot (Along B.val) := (hℬ.1 B.val B.property).cofinite_inf_principal_neBot
  exact tendsto_nhds_unique (operator_family_matrix_tendsto h𝒜 T A hAE B)
    (hadmit A.val ⟨A.property, hAA⟩ B.val ⟨B.property, hBB⟩)

/-- The paper's full statement, proved directly for Mrówka spaces using
disjoint tails and generator determination. General Lemma 4.17 is proved
separately in ScatteredOperators and is not needed for this direct proof. -/
theorem lemma_4_18_proof (𝕜 : Type) [RCLike 𝕜] (𝒜 ℬ : Set (Set ℕ)) :
    Lemma_4_18 𝕜 𝒜 ℬ := by
  intro h𝒜 hℬ T
  constructor
  · let E := operatorExceptionalFamily h𝒜 T
    refine ⟨Subtype.val '' E, ?_, (operatorExceptionalFamily_countable h𝒜 T).image _, ?_, ?_⟩
    · rintro _ ⟨A, _, rfl⟩
      exact A.property
    · intro A hA
      have hn : A ∉ E := fun h => hA ⟨A, h, rfl⟩
      exact ⟨familyVector 𝕜 𝒜 h𝒜 A, familyVector_isNeighborhoodIndicator 𝕜 𝒜 h𝒜 A,
        operator_family_matrix h𝒜 T A hn⟩
    · rintro A ⟨hA, hAE⟩ B hB
      have hn : (⟨A, hA⟩ : 𝒜) ∉ E := fun h => hAE ⟨⟨A, hA⟩, h, rfl⟩
      exact not_not.mpr ⟨T (familyVector 𝕜 𝒜 h𝒜 ⟨A, hA⟩) (Sum.inr ⟨B, hB⟩),
        operator_family_matrix_tendsto h𝒜 T ⟨A, hA⟩ hn ⟨B, hB⟩⟩
  · rintro ⟨𝒜', ℬ', _, _, hA, hB, hadmit⟩
    exact factorsThroughCZero_of_admission h𝒜 hℬ T 𝒜' ℬ' hA hB hadmit

end Posets
