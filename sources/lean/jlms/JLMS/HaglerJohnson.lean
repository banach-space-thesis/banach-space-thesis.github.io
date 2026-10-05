import JLMS.SignTreeConstruction
import JLMS.BlockCZeroProjection

/-!
# Hagler–Johnson normalized weak-star-null blocks

Stabilize a bounded dual sequence under further blocking. Radius zero gives
pointwise nullity. If the radius is positive, rescale it to one and construct
the binary sign tree, hence an ℓ¹ embedding. The no-ℓ¹ hypothesis rules out
this second alternative and supplies exactly the blocks used by the
Galego–Plichko projection construction.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem exists_normalizedBlock_pointwise_null
    (hX : ¬ ContainsEllOne 𝕜 X) (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ d : NormalizedBlockSystem 𝕜,
      ∀ x, Tendsto (fun n => d.applyDual f n x) atTop (𝓝 0) := by
  obtain ⟨d, hd⟩ := exists_block_radius_stable f hC hf
  let g := d.applyDual f
  have hg : ∀ n, ‖g n‖ ≤ C := d.norm_applyDual_le f hf
  let r := dualAsymptoticRadius g
  have hr : 0 ≤ r := dualAsymptoticRadius_nonneg g hC hg
  by_cases hr0 : r = 0
  · exact ⟨d, (dualAsymptoticRadius_eq_zero_iff g hC hg).mp hr0⟩
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let a : 𝕜 := ((r⁻¹ : ℝ) : 𝕜)
    let g' (n : ℕ) := a • g n
    have hbound : ∀ n, ‖g' n‖ ≤ ‖a‖ * C := by
      intro n
      change ‖a • g n‖ ≤ ‖a‖ * C
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hg n) (norm_nonneg a)
    have hstable (b : NormalizedBlockSystem 𝕜) : dualAsymptoticRadius (b.applyDual g') = 1 := by
      have heq : b.applyDual g' = fun n => a • b.applyDual g n := by
        funext n
        exact b.applyDual_smul g a n
      rw [heq, dualAsymptoticRadius_smul _ hC (b.norm_applyDual_le g hg) a, hd]
      change ‖a‖ * r = 1
      simp only [a, RCLike.norm_ofReal, abs_inv, abs_of_pos hrpos, inv_mul_cancel₀ hr0]
    exact (hX (containsEllOne_of_stable_radius_one g'
      (mul_nonneg (norm_nonneg a) hC) hbound hstable)).elim

theorem dualNormalizedBlockNull_of_not_containsEllOne (hX : ¬ ContainsEllOne 𝕜 X) :
    DualNormalizedBlockNull (𝕜 := 𝕜) (X := X) := by
  intro f ⟨C, hf⟩
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hf 0)
  obtain ⟨d, hd⟩ := exists_normalizedBlock_pointwise_null hX f hC hf
  exact ⟨d.support, d.coefficient, d.disjoint, d.mass_one, hd⟩

end JLMS
