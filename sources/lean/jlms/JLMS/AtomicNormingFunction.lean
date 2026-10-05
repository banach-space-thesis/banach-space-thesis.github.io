import JLMS.AtomicDual
import JLMS.PhaseFunctions
import JLMS.ScatteredTopology

/-!
# The last step of Section 6: finite atoms to a supported norming function

The proof follows the paper: retain the large finite set A, truncate the rest
of the functional, shrink the given neighborhoods to avoid the remaining finite
atoms H, and use scalar phases on A. The discarded tail contributes less than θ.
This is separate from the still open infinite diagonal selection in Lemma 6.1.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

theorem exists_supported_atomic_norming_function
    (M : AtomicDualModel 𝕜 K) (hK : IsScattered K)
    (φ : CZero 𝕜 K →L[𝕜] 𝕜) (A : Finset K)
    (U : NeighborhoodFamily (fun k : ↥A => (k : K)))
    {r θ : ℝ} (hθ : 0 < θ) (hlarge : r + θ < ‖atomicRestriction M (A : Set K) φ‖) :
    ∃ η : CZero 𝕜 K, ‖η‖ ≤ 1 ∧
      Function.support η ⊆ ⋃ k, U.sets k ∧ r < ‖φ η‖ := by
  obtain ⟨s, hs⟩ := exists_finite_atomicRestriction_tail M φ hθ
  let H := s \ A
  let t := A ∪ H
  have hst : (s : Set K) ⊆ (t : Set K) := by
    intro k hk
    by_cases hka : k ∈ A <;> simp [t, H, hk, hka]
  have htail : ‖φ - atomicRestriction M (t : Set K) φ‖ < θ :=
    (atomicRestriction_tail_norm_mono M hst φ).trans_lt hs
  have hopen : IsOpen (H : Set K)ᶜ := H.finite_toSet.isClosed.isOpen_compl
  have hp (k : ↥A) : (k : K) ∈ (H : Set K)ᶜ := by simp [H]
  obtain ⟨V, hV⟩ := exists_neighborhoodFamily_shrink hK U hopen hp
  let η := neighborhoodPhaseFunction V (fun k : ↥A => M.representation φ k.val)
  have hη : ‖η‖ ≤ 1 := neighborhoodPhaseFunction_norm_le _ _
  have heval (k : K) (hk : k ∈ A) : η k = scalarPhase (M.representation φ k) :=
    neighborhoodPhaseFunction_at_point V _ ⟨k, hk⟩
  have hzero (k : K) (hk : k ∈ H) : η k = 0 := by
    by_contra hn
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (neighborhoodPhaseFunction_support_subset V _ hn)
    exact (hV i hi).2 hk
  have hdisj : Disjoint A H := by
    apply Finset.disjoint_left.mpr
    intro k hk hkH
    exact (Finset.mem_sdiff.mp hkH).2 hk
  have hpair : atomicRestriction M (t : Set K) φ η =
      (‖atomicRestriction M (A : Set K) φ‖ : 𝕜) := by
    rw [atomicRestriction_finset_apply]
    rw [Finset.sum_union hdisj]
    have hz : ∑ k ∈ H, M.representation φ k * η k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hzero k hk, mul_zero]
    rw [hz, add_zero, atomicRestriction_norm, restrictionL1_finset_norm]
    rw [RCLike.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [heval k hk, mul_comm, scalarPhase_mul]
  have herror : ‖(φ - atomicRestriction M (t : Set K) φ) η‖ < θ := by
    have hb := (φ - atomicRestriction M (t : Set K) φ).le_opNorm η
    have hb' := mul_le_mul_of_nonneg_left hη (norm_nonneg (φ - atomicRestriction M (t : Set K) φ))
    exact (hb.trans (by simpa only [mul_one] using hb')).trans_lt htail
  refine ⟨η, hη, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (neighborhoodPhaseFunction_support_subset V _ hk)
    exact Set.mem_iUnion.mpr ⟨i, (hV i hi).1⟩
  · have hb := norm_sub_norm_le (atomicRestriction M (t : Set K) φ η) (φ η)
    have hvalue : ‖atomicRestriction M (t : Set K) φ η‖ =
        ‖atomicRestriction M (A : Set K) φ‖ := by
      rw [hpair, RCLike.norm_ofReal]
      exact abs_of_nonneg (norm_nonneg (atomicRestriction M (A : Set K) φ))
    rw [hvalue] at hb
    have herr' : ‖atomicRestriction M (t : Set K) φ η - φ η‖ < θ := by
      rw [norm_sub_rev]
      exact herror
    linarith

end JLMS
