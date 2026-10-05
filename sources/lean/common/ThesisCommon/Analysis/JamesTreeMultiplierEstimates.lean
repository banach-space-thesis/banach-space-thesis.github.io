import ThesisCommon.Analysis.JamesTreeDisjointMasks
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Finite-chain oscillation bounds imply genuine multiplier estimates.
The coefficient condition is scalar and finite; the resulting bounded map
is constructed on c00 before completion. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

theorem literalJamesTreeMaskClosed_any (A : Set DyadicTreeNode) :
    JamesTreeMaskClosed literalTreeSegmentFamily A := by
  intro B hB hne
  exact ⟨hne, fun s hs t ht =>
    hB.2 s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1⟩

theorem consecutiveJamesTreeMaskClosed_convex (A : Set DyadicTreeNode)
    (hA : ∀ s ∈ A, ∀ t ∈ A, ∀ u, s.IsPrefix u → u.IsPrefix t → u ∈ A) :
    JamesTreeMaskClosed consecutiveTreeSegmentFamily A := by
  intro B hB hne
  refine ⟨⟨hne, fun s hs t ht =>
    hB.1.2 s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1⟩, ?_⟩
  intro s hs t ht u hsu hut
  obtain ⟨hsB, hsA⟩ := Finset.mem_filter.mp hs
  obtain ⟨htB, htA⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hB.2 s hsB t htB u hsu hut, hA s hsA t htA u hsu hut⟩

theorem consecutiveJamesTreeMaskClosed_segment {A : Finset DyadicTreeNode}
    (hA : IsConsecutiveTreeSegment A) :
    JamesTreeMaskClosed consecutiveTreeSegmentFamily (A : Set DyadicTreeNode) :=
  consecutiveJamesTreeMaskClosed_convex _ hA.2

namespace JamesTreePreSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem segment_sum_norm_le (A : Finset DyadicTreeNode) (hA : S.allows A)
    (a : JamesTreePreSpace 𝕜 p S) : ‖∑ t ∈ A, a t‖ ≤ ‖a‖ := by
  have htest := jamesTree_partial_test_norm_le p a (fun _ : Fin 1 => A)
    (fun _ _ => hA) (fun i j hij => (hij (Subsingleton.elim i j)).elim)
  exact (PiLp.norm_apply_le (WithLp.toLp p.val
    (fun _ : Fin 1 => ∑ t ∈ A, a t)) (0 : Fin 1)).trans htest

def multiplierLinear (d : DyadicTreeNode → 𝕜) :
    JamesTreePreSpace 𝕜 p S →ₗ[𝕜] JamesTreePreSpace 𝕜 p S :=
  Finsupp.linearCombination 𝕜 (fun t => single t (d t))

@[simp] theorem multiplierLinear_apply (d : DyadicTreeNode → 𝕜)
    (a : JamesTreePreSpace 𝕜 p S) (s : DyadicTreeNode) :
    multiplierLinear d a s = d s * a s := by
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_apply, mul_zero]
  | add a b ha hb =>
    simp only [map_add, add_apply, ha, hb]
    exact (mul_add _ _ _).symm
  | single t c =>
    change (Finsupp.linearCombination 𝕜 (fun t => single (p := p) (S := S) t (d t)))
      (Finsupp.single t c) s = d s * single (p := p) (S := S) t c s
    rw [Finsupp.linearCombination_single]
    simp only [smul_apply, single_apply, smul_eq_mul]
    split_ifs with h
    · subst t; exact mul_comm _ _
    · simp

theorem multiplier_segment_norm_le (d : DyadicTreeNode → 𝕜)
    (A : Finset DyadicTreeNode) (hA : S.allows A)
    (hmask : JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (a : JamesTreePreSpace 𝕜 p S) (c : 𝕜) :
    ‖∑ t ∈ A, d t * a t‖ ≤
      (‖c‖ + ∑ t ∈ A, ‖d t - c‖) * ‖mask (A : Set DyadicTreeNode) hmask a‖ := by
  classical
  let y := mask (A : Set DyadicTreeNode) hmask a
  have hy (t) (ht : t ∈ A) : y t = a t := by
    dsimp only [y]
    rw [mask_apply]
    exact if_pos ht
  have hsum : ‖∑ t ∈ A, a t‖ ≤ ‖y‖ := by
    simpa only [Finset.sum_congr rfl (fun t ht => hy t ht)] using segment_sum_norm_le A hA y
  have hcoord (t) (ht : t ∈ A) : ‖a t‖ ≤ ‖y‖ := by
    rw [← hy t ht]; exact norm_apply_le y t
  have heq : (∑ t ∈ A, d t * a t) = c * (∑ t ∈ A, a t) + ∑ t ∈ A, (d t-c)*a t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [heq]
  calc
    _ ≤ ‖c * (∑ t ∈ A, a t)‖ + ‖∑ t ∈ A, (d t-c)*a t‖ := norm_add_le _ _
    _ ≤ ‖c‖ * ‖y‖ + ∑ t ∈ A, ‖d t-c‖ * ‖y‖ := by
      apply add_le_add
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hcoord t ht) (norm_nonneg _))
    _ = _ := by rw [add_mul, Finset.sum_mul]

theorem multiplierLinear_norm_le (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (d : DyadicTreeNode → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ A, S.allows A → ∃ c : 𝕜, ‖c‖ + ∑ t ∈ A, ‖d t-c‖ ≤ C)
    (a : JamesTreePreSpace 𝕜 p S) : ‖multiplierLinear d a‖ ≤ C * ‖a‖ := by
  classical
  apply norm_le
  intro T
  let A (j : Fin T.count) : Set DyadicTreeNode := (T.segment j : Set DyadicTreeNode)
  let hA j := hS _ (T.allowed j)
  let v := WithLp.toLp p.val (fun j => ‖mask (A j) (hA j) a‖)
  have hbound (j : Fin T.count) :
      ‖jamesTreeTestMap 𝕜 p T (coefficients (multiplierLinear d a)) j‖ ≤
        C * ‖mask (A j) (hA j) a‖ := by
    obtain ⟨c,hc⟩ := hd _ (T.allowed j)
    change ‖∑ t ∈ T.segment j, multiplierLinear d a t‖ ≤ _
    simp only [multiplierLinear_apply]
    exact (multiplier_segment_norm_le d _ (T.allowed j) (hA j) a c).trans
      (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have hv : ‖v‖ ≤ ‖a‖ := disjoint_masks_norm_le hp A hA
    (fun _ _ hij => Finset.disjoint_coe.mpr (T.disjoint hij)) a
  have hnorm : ‖jamesTreeTestMap 𝕜 p T (coefficients (multiplierLinear d a))‖ ≤
      ‖C • v‖ := by
    rw [PiLp.norm_eq_sum hp, PiLp.norm_eq_sum hp]
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    apply Real.rpow_le_rpow (norm_nonneg _) _ hp.le
    change _ ≤ ‖C * ‖mask (A j) (hA j) a‖‖
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC,
      abs_of_nonneg (norm_nonneg _)] using hbound j
  apply hnorm.trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_left hv hC

end JamesTreePreSpace
end ThesisCommon
