import Posets.FamilyTails

/-! A functional killing the isolated vectors is nonzero on only countably
many family indicators. Finite disjoint tails give the stronger ℓ¹ bound. -/

noncomputable section
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem functional_family_finite_bound (h𝒜 : IsAlmostDisjoint 𝒜)
    (φ : Space 𝕜 𝒜 →L[𝕜] 𝕜) (hz : ∀ n, φ (isolatedVector 𝕜 𝒜 n) = 0)
    (F : Finset 𝒜) : ∑ A ∈ F, ‖φ (familyVector 𝕜 𝒜 h𝒜 A)‖ ≤ ‖φ‖ := by
  classical
  obtain ⟨G, hG⟩ := JFA.exists_pairwise_disjoint_mrowka_tails h𝒜
    (Subtype.val : F → 𝒜) Subtype.val_injective
  let η : F → Space 𝕜 𝒜 := fun A => familyTailVector h𝒜 A.val (G A)
  have hunit : ∀ A, ‖η A‖ ≤ 1 := fun A => norm_familyTailVector_le h𝒜 A.val (G A)
  have hd : Pairwise fun A B => Disjoint (Function.support (η A)) (Function.support (η B)) :=
    fun A B h => (hG h).mono (familyTailVector_support_subset h𝒜 A.val (G A))
      (familyTailVector_support_subset h𝒜 B.val (G B))
  let c : F → 𝕜 := fun A => normingPhase (φ (familyVector 𝕜 𝒜 h𝒜 A.val))
  let f : Space 𝕜 𝒜 := ∑ A : F, c A • η A
  have hf : ‖f‖ ≤ 1 := JFA.norm_sum_smul_disjointCzero_le η hunit hd Finset.univ c
    zero_le_one (fun _ _ => norm_normingPhase_le _)
  have heval : φ f = ((∑ A : F, ‖φ (familyVector 𝕜 𝒜 h𝒜 A.val)‖ : ℝ) : 𝕜) := by
    simp only [f, map_sum, map_smul, η, functional_familyTailVector h𝒜 φ hz, smul_eq_mul]
    simp_rw [show ∀ A : F, c A * φ (familyVector 𝕜 𝒜 h𝒜 A.val) =
        (‖φ (familyVector 𝕜 𝒜 h𝒜 A.val)‖ : 𝕜) from
      fun A => by rw [mul_comm]; exact mul_normingPhase _]
  have hb : (∑ A : F, ‖φ (familyVector 𝕜 𝒜 h𝒜 A.val)‖) ≤ ‖φ‖ := calc
    _ = ‖φ f‖ := by
      rw [heval, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖φ‖ * ‖f‖ := φ.le_opNorm f
    _ ≤ ‖φ‖ := by nlinarith [norm_nonneg φ]
  rw [← Finset.sum_attach F (fun A => ‖φ (familyVector 𝕜 𝒜 h𝒜 A)‖)]
  exact hb

theorem functional_family_summable (h𝒜 : IsAlmostDisjoint 𝒜)
    (φ : Space 𝕜 𝒜 →L[𝕜] 𝕜) (hz : ∀ n, φ (isolatedVector 𝕜 𝒜 n) = 0) :
    Summable (fun A : 𝒜 => ‖φ (familyVector 𝕜 𝒜 h𝒜 A)‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (functional_family_finite_bound h𝒜 φ hz)

theorem functional_family_support_countable (h𝒜 : IsAlmostDisjoint 𝒜)
    (φ : Space 𝕜 𝒜 →L[𝕜] 𝕜) (hz : ∀ n, φ (isolatedVector 𝕜 𝒜 n) = 0) :
    {A : 𝒜 | φ (familyVector 𝕜 𝒜 h𝒜 A) ≠ 0}.Countable := by
  simpa only [Function.support, norm_ne_zero_iff] using
    (functional_family_summable h𝒜 φ hz).countable_support

end Posets
