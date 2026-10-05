import Posets.AcceptanceDichotomyDecidability
import Posets.MainFewOperatorsConstruction

/-! The main poset theorem and its continuum-sized nonisomorphism corollary,
with the acceptance/rejection dichotomy fully discharged. -/

noncomputable section
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

/-- Theorem 1.1, for every poset admitting the printed order embedding. -/
theorem theorem_1_1_proof (P : Type*) [PartialOrder P] : Theorem_1_1 𝕜 P :=
  theorem_1_1_of_lemma_5_2 (fun M => lemma_5_2_proof closedTreeFamily M) P

/-- The constructed families have exactly continuum members, as used in the
applications; their connecting maps satisfy the full few-operator condition. -/
theorem continuum_fewOperators {P : Type*} [PartialOrder P] (e : P ↪o Set (Set ℕ)) :
    ∃ 𝒜 : P → Set (Set ℕ),
      (∀ t, IsAlmostDisjoint (𝒜 t) ∧ JFA.HasContinuumSize (𝒜 t)) ∧
      ∃ j : ∀ s t, Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t),
        FewOperators 𝕜 (fun t => Space 𝕜 (𝒜 t)) j :=
  continuum_fewOperators_of_lemma_5_2 (fun M => lemma_5_2_proof closedTreeFamily M) e

/-- Corollary 1.2, including the exact continuum cardinality of each family. -/
theorem corollary_1_2_proof : Corollary_1_2 𝕜 :=
  corollary_1_2_of_lemma_5_2 (fun M => lemma_5_2_proof closedTreeFamily M)

end Posets
