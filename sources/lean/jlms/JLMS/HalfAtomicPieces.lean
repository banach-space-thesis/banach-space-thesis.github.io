import JLMS.AtomicApplications

/-!
# Proposition 5.2: large finite atoms from the primal essential norm

This follows the original argument, including the factor two. A finite
neighborhood projection removes previously used points. Half of the remaining
unit-ball function still belongs to the unit ball, and Hahn–Banach supplies the
dual functional. Atomic truncation then gives the next disjoint finite piece.
Rudin's representation remains the explicit data input M.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_large_dual_piece_avoiding_of_primal
    (M : AtomicDualModel 𝕜 K) (hK : IsScattered K) (T : CZero 𝕜 K →L[𝕜] X)
    {r : ℝ} (hr : 0 ≤ r) (hT : 2 * r < essentialNorm T) (s : Finset K) :
    ∃ φ : X →L[𝕜] 𝕜, ∃ A : Finset K, ‖φ‖ ≤ 1 ∧
      (A : Set K) ⊆ Function.support (M.representation (banachAdjoint T φ)) ∧
      Disjoint A s ∧ r < ‖atomicRestriction M (A : Set K) (banachAdjoint T φ)‖ := by
  obtain ⟨U⟩ := exists_neighborhoodFamily hK (fun k : ↥s => (k : K)) Subtype.val_injective
  let P := neighborhoodProjection (𝕜 := 𝕜) U
  let Q := T.comp (ContinuousLinearMap.id 𝕜 (CZero 𝕜 K) - P)
  have hc : IsCompactOperator (T.comp P) := (neighborhoodProjection_compact U).clm_comp T
  have heq : T - T.comp P = Q := by
    ext f
    simp [Q]
  have hnorm : 2 * r < ‖Q‖ := by
    have hb := essentialNorm_le_norm_sub T (T.comp P) hc
    rw [heq] at hb
    exact hT.trans_le hb
  obtain ⟨ζ, hζ, hζlarge⟩ := exists_unit_norm_image_gt Q (by linarith) hnorm
  let a : 𝕜 := (1 / 2 : ℝ)
  have ha : ‖a‖ = 1 / 2 := by dsimp [a]; rw [RCLike.norm_ofReal]; norm_num
  let η := a • ((ContinuousLinearMap.id 𝕜 (CZero 𝕜 K) - P) ζ)
  letI : NormSMulClass 𝕜 (CZero 𝕜 K) :=
    @NormedSpace.toNormSMulClass 𝕜 (CZero 𝕜 K) _ _ _
  have hη : ‖η‖ ≤ 1 := by
    have hb := (ContinuousLinearMap.id 𝕜 (CZero 𝕜 K) - P).le_opNorm ζ
    have hp := norm_id_sub_neighborhoodProjection_le_two (𝕜 := 𝕜) U
    rw [hζ, mul_one] at hb
    change ‖a • ((ContinuousLinearMap.id 𝕜 (CZero 𝕜 K) - P) ζ)‖ ≤ 1
    rw [norm_smul, ha]
    have hb' : ‖(ContinuousLinearMap.id 𝕜 (CZero 𝕜 K) - P) ζ‖ ≤ 2 := hb.trans hp
    linarith
  have hTη : r < ‖T η‖ := by
    have he : T η = a • Q ζ := by simp [η, Q]
    rw [he, norm_smul, ha]
    linarith
  obtain ⟨φ, hφ, hφvalue⟩ := exists_dual_vector'' 𝕜 (T η)
  let ψ := banachAdjoint T φ
  have hψ : r < ‖ψ η‖ := by
    change r < ‖φ (T η)‖
    rw [hφvalue, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg (T η))]
    exact hTη
  have hzero : atomicRestriction M (s : Set K) ψ η = 0 := by
    rw [atomicRestriction_finset_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hηk : η k = 0 := by
      have hp := neighborhoodProjection_at_point (𝕜 := 𝕜) U ζ ⟨k, hk⟩
      simp [η, P, hp]
    rw [hηk, mul_zero]
  have hcompl : atomicRestriction M (s : Set K)ᶜ ψ η = ψ η := by
    rw [← atomicRestriction_compl]
    simp only [ContinuousLinearMap.sub_apply, hzero, sub_zero]
  have hmass : r < ‖atomicRestriction M (s : Set K)ᶜ ψ‖ := by
    have hb := (atomicRestriction M (s : Set K)ᶜ ψ).le_opNorm η
    rw [hcompl] at hb
    have hb' := mul_le_mul_of_nonneg_left hη (norm_nonneg (atomicRestriction M (s : Set K)ᶜ ψ))
    exact hψ.trans_le (hb.trans (by simpa only [mul_one] using hb'))
  rw [atomicRestriction_norm] at hmass
  obtain ⟨A, hA, hlarge⟩ := exists_finite_restrictionL1_mass
    (restrictionL1 (s : Set K)ᶜ (M.representation ψ)) hmass
  have havoid : ∀ k ∈ A, k ∉ s := by
    intro k hk hks
    exact hA hk (by simp [hks])
  have hsupp : (A : Set K) ⊆ Function.support (M.representation ψ) := by
    intro k hk
    have hn := hA hk
    simpa [havoid k hk] using hn
  have he : restrictionL1 (A : Set K)
      (restrictionL1 (s : Set K)ᶜ (M.representation ψ)) = restrictionL1 (A : Set K) (M.representation ψ) := by
    ext k
    by_cases hk : k ∈ A <;> simp [hk, havoid k]
  rw [he] at hlarge
  exact ⟨φ, A, hφ, hsupp, Finset.disjoint_left.mpr havoid, by
    simpa only [atomicRestriction_norm] using hlarge⟩

/-- Proposition 5.2 with r = δ + 2θ. The factor two comes from the original
finite-neighborhood projection estimate rather than a Schauder assumption. -/
theorem exists_disjoint_large_dual_atoms_of_primal
    (M : AtomicDualModel 𝕜 K) (hK : IsScattered K) (T : CZero 𝕜 K →L[𝕜] X)
    {r : ℝ} (hr : 0 ≤ r) (hT : 2 * r < essentialNorm T) :
    ∃ φ : ℕ → (X →L[𝕜] 𝕜), ∃ A : ℕ → Finset K,
      (∀ j, ‖φ j‖ ≤ 1) ∧
      (∀ j, (A j : Set K) ⊆ Function.support (M.representation (banachAdjoint T (φ j)))) ∧
      (Pairwise fun i j => Disjoint (A i) (A j)) ∧
      ∀ j, r < ‖atomicRestriction M (A j : Set K) (banachAdjoint T (φ j))‖ := by
  let P (φ : X →L[𝕜] 𝕜) (A : Finset K) := ‖φ‖ ≤ 1 ∧
    (A : Set K) ⊆ Function.support (M.representation (banachAdjoint T φ)) ∧
    r < ‖atomicRestriction M (A : Set K) (banachAdjoint T φ)‖
  have hnext (s : Finset K) : ∃ φ, ∃ A, P φ A ∧ Disjoint A s := by
    obtain ⟨φ, A, hφ, hsupp, hd, hmass⟩ := exists_large_dual_piece_avoiding_of_primal M hK T hr hT s
    exact ⟨φ, A, ⟨hφ, hsupp, hmass⟩, hd⟩
  obtain ⟨φ, A, hP, hd⟩ := exists_disjoint_finite_witnesses P hnext
  exact ⟨φ, A, fun j => (hP j).1, fun j => (hP j).2.1, hd, fun j => (hP j).2.2⟩

end JLMS
