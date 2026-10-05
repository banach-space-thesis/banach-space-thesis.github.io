import Posets.AcceptanceDichotomyAmalgamation
import Posets.Definitions

/-! Concrete assertions in Remarks 4.14, 6.2, 6.3 and 6.5.
The original acceptance convention is Definition 15 of Koszmider--Laustsen:
each union of two members accepts the matrix on itself. -/

noncomputable section
open Set
open scoped BigOperators
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

/-- Remark 4.14, with exactly the earlier pairwise-union convention. -/
theorem remark_4_14_acceptance_iff {𝒜 : Set (Set ℕ)} {M : ScalarMatrix 𝕜}
    (hM : HasBoundedRows 𝕜 M) :
    Accepts 𝕜 𝒜 𝒜 M ↔
      ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, AcceptsPair 𝕜 (A ∪ B) (A ∪ B) M := by
  constructor
  · intro h A hA B hB
    exact h A hA B hB A hA B hB
  · intro h
    apply accepts_of_pairwise_acceptsPair hM
    intro A hA B hB
    exact acceptsPair_mono (h A hA B hB) subset_union_left subset_union_right

/-- The identification with an image in Remark 6.2 is justified by injectivity. -/
theorem remark_6_2_embedding_injective {P : Type*} [PartialOrder P]
    {X : P → Type*} [∀ t, NormedAddCommGroup (X t)] [∀ t, NormedSpace 𝕜 (X t)]
    {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)
    {s t : P} (hst : s ≤ t) : Function.Injective (ι s t) :=
  (h.2.1 s t hst).injective

/-- The zero convention in Remark 6.3 is part of the few-operator data. -/
theorem remark_6_3_off_order_zero {P : Type*} [PartialOrder P]
    {X : P → Type*} [∀ t, NormedAddCommGroup (X t)] [∀ t, NormedSpace 𝕜 (X t)]
    {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)
    {s t : P} (hst : ¬ s ≤ t) : ι s t = 0 := h.2.2.2.1 s t hst

/-- The opposite-order zero pattern in Remark 6.5, on the original points. -/
theorem remark_6_5_zero_pattern {P : Type*} [PartialOrder P]
    (f : IncidenceAlgebra 𝕜 Pᵒᵈ) {s t : P} (hst : ¬ t ≤ s) : f s t = 0 :=
  f.eq_zero_of_not_le' hst

/-- The opposite-order convolution in Remark 6.5. -/
theorem remark_6_5_convolution {P : Type*} [PartialOrder P] [LocallyFiniteOrder P]
    (f g : IncidenceAlgebra 𝕜 Pᵒᵈ) (s t : P) :
    (f * g) s t = ∑ r ∈ (Finset.Icc t s : Finset P), f s r * g r t := by
  exact IncidenceAlgebra.mul_apply f g s t

end Posets
