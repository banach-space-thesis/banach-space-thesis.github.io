import ThesisCommon.Analysis.OnePointContinuousDecomposition
import ThesisCommon.Analysis.CountableCompactOnePoint
import ThesisCommon.Analysis.ScalarSequencePrimary
import ThesisCommon.Analysis.EllOneSelfSimilarPreservation

/-! Unconditional Banach-space consequences for a countably infinite compact
Hausdorff space with one possible nonisolated point. The actual c₀ equivalence
supplies base-space UPFP, primariness, and the c₀ and ℓ₁ preservation cases. -/

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
variable [Countable K] [Infinite K]
variable (p : K) (hp : ∀ x, x ≠ p → IsOpen ({x} : Set K))

def countableCompactOnePointCZeroEquiv : C(K, 𝕜) ≃L[𝕜] CZeroSum 𝕜 :=
  (continuousMapHomeomorphEquiv (countableCompactOnePointHomeomorph p hp)).trans
    onePointContinuousCZeroEquiv

def countableCompactOnePointSelfEquiv : C(K, 𝕜) ≃L[𝕜] CZeroSum C(K, 𝕜) :=
  (countableCompactOnePointCZeroEquiv p hp).trans
    (cZeroFlattenEquiv.symm.trans
      (cZeroMapEquiv (ι := ℕ) (countableCompactOnePointCZeroEquiv p hp).symm))

include p hp

theorem countableCompactOnePoint_hasUPFP : HasUPFP 𝕜 C(K, 𝕜) :=
  scalar_cZero_hasUPFP.of_equiv (countableCompactOnePointCZeroEquiv p hp).symm

theorem countableCompactOnePoint_primary : IsPrimary 𝕜 C(K, 𝕜) :=
  (countableCompactOnePoint_hasUPFP p hp).isPrimary_of_sequenceSelfSimilar
    (Or.inr ⟨countableCompactOnePointSelfEquiv p hp⟩)

theorem countableCompactOnePoint_cZero_upfp_primary :
    HasUPFP 𝕜 (CZeroSum C(K, 𝕜)) ∧ IsPrimary 𝕜 (CZeroSum C(K, 𝕜)) := by
  have h := (countableCompactOnePoint_hasUPFP (𝕜 := 𝕜) p hp).of_equiv
    (countableCompactOnePointSelfEquiv p hp)
  exact ⟨h, h.cZero_isPrimary⟩

theorem countableCompactOnePoint_ellOne_upfp_primary :
    HasUPFP 𝕜 (EllOneSum ℕ C(K, 𝕜)) ∧ IsPrimary 𝕜 (EllOneSum ℕ C(K, 𝕜)) := by
  have h := (countableCompactOnePoint_hasUPFP (𝕜 := 𝕜) p hp).ellOne_of_cZero_equiv
    (countableCompactOnePointSelfEquiv p hp)
  exact ⟨h, h.lp_isPrimary⟩

omit hp in
theorem countableCompact_derived_singleton_upfp_primary
    (hderiv : derivedSet (Set.univ : Set K) = {p}) :
    HasUPFP 𝕜 C(K, 𝕜) ∧ IsPrimary 𝕜 C(K, 𝕜) := by
  have hiso : ∀ x, x ≠ p → IsOpen ({x} : Set K) := fun x hx =>
    isOpen_singleton_of_not_mem_derivedSet_univ x (by simpa [hderiv] using hx)
  exact ⟨countableCompactOnePoint_hasUPFP p hiso, countableCompactOnePoint_primary p hiso⟩

end ThesisCommon
