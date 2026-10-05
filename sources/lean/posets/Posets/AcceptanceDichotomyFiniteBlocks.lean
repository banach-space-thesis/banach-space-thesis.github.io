import Posets.AcceptanceDichotomyMatrixAlgebra
import ThesisCommon.Analysis.RCLikeEllOneSchurBlocks
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

/-! Finite indicator tests capture a fixed portion of the absolute row mass. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
namespace Posets
variable {𝕜 I : Type*} [RCLike 𝕜]

theorem scalar_norm_le_abs_re_add_abs_im (z : 𝕜) :
    ‖z‖ ≤ |RCLike.re z| + |RCLike.im z| := by
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    by_cases h : (RCLike.I : 𝕜) = 0
    · simp [h]
    · exact (RCLike.norm_I_of_ne_zero h).le
  calc
    ‖z‖ = ‖(RCLike.re z : 𝕜) + (RCLike.im z : 𝕜) * RCLike.I‖ := by
      rw [RCLike.re_add_im]
    _ ≤ ‖(RCLike.re z : 𝕜)‖ + ‖(RCLike.im z : 𝕜) * RCLike.I‖ := norm_add_le _ _
    _ ≤ |RCLike.re z| + |RCLike.im z| := by
      rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal]
      simpa using add_le_add_left (mul_le_mul_of_nonneg_left hI (abs_nonneg (RCLike.im z)))
        |RCLike.re z|

theorem sum_abs_addHom_le_two_mul (E : Finset I) (z : I → 𝕜) (φ : 𝕜 →+ ℝ)
    (hφ : ∀ x, |φ x| ≤ ‖x‖) (C : ℝ)
    (hC : ∀ F : Finset I, F ⊆ E → ‖∑ i ∈ F, z i‖ ≤ C) :
    ∑ i ∈ E, |φ (z i)| ≤ 2 * C := by
  let P := E.filter (fun i => 0 ≤ φ (z i))
  let N := E.filter (fun i => ¬ 0 ≤ φ (z i))
  have hp : (∑ i ∈ P, |φ (z i)|) = φ (∑ i ∈ P, z i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i hi => abs_of_nonneg (Finset.mem_filter.mp hi).2)
  have hn : (∑ i ∈ N, |φ (z i)|) = -φ (∑ i ∈ N, z i) := by
    rw [map_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i hi => abs_of_nonpos
      (le_of_not_ge (Finset.mem_filter.mp hi).2))
  have hsplit : (∑ i ∈ E, |φ (z i)|) =
      (∑ i ∈ P, |φ (z i)|) + ∑ i ∈ N, |φ (z i)| := by
    exact (Finset.sum_filter_add_sum_filter_not E (fun i => 0 ≤ φ (z i)) _).symm
  rw [hsplit, hp, hn]
  have hp' := (le_abs_self (φ (∑ i ∈ P, z i))).trans
    ((hφ _).trans (hC P (Finset.filter_subset _ _)))
  have hn' := (neg_le_abs (φ (∑ i ∈ N, z i))).trans
    ((hφ _).trans (hC N (Finset.filter_subset _ _)))
  linarith

/-- Among the subsets of a finite scalar family, one indicator sum captures
at least one quarter of its total absolute mass, over both ℝ and ℂ. -/
theorem exists_subset_four_mul_norm_sum (E : Finset I) (z : I → 𝕜) :
    ∃ F : Finset I, F ⊆ E ∧ (∑ i ∈ E, ‖z i‖) ≤ 4 * ‖∑ i ∈ F, z i‖ := by
  obtain ⟨F, hF, hmax⟩ := E.powerset.exists_max_image (fun G : Finset I => ‖∑ i ∈ G, z i‖)
    (by exact ⟨∅, Finset.empty_mem_powerset E⟩)
  have hC (G : Finset I) (hG : G ⊆ E) : ‖∑ i ∈ G, z i‖ ≤ ‖∑ i ∈ F, z i‖ :=
    hmax G (Finset.mem_powerset.mpr hG)
  have hr := sum_abs_addHom_le_two_mul E z RCLike.reLm.toAddMonoidHom
    RCLike.abs_re_le_norm _ hC
  have hi := sum_abs_addHom_le_two_mul E z RCLike.imLm.toAddMonoidHom
    RCLike.abs_im_le_norm _ hC
  refine ⟨F, Finset.mem_powerset.mp hF, ?_⟩
  have hbound := Finset.sum_le_sum (fun i (_ : i ∈ E) => scalar_norm_le_abs_re_add_abs_im (z i))
  rw [Finset.sum_add_distrib] at hbound
  change (∑ i ∈ E, |RCLike.re (z i)|) ≤ _ at hr
  change (∑ i ∈ E, |RCLike.im (z i)|) ≤ _ at hi
  linarith

end Posets
