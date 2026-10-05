import ThesisCommon.Analysis.DyadicDelayedFork
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The actual finite-support readback over selected-subtree cells. Each
ambient coefficient is assigned to at most one cell, so this is a genuine
linear map on c00; its norm bound follows by lifting disjoint segment tests. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.JamesTreePreSpace
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def delayedReadAtom (e : DyadicDelayedFork) (t : DyadicTreeNode) : JamesTreePreSpace 𝕜 p S :=
  if h : ∃ s, t ∈ dyadicRootedCell e.fork s then single (Classical.choose h) 1 else 0

theorem delayedReadAtom_apply (e : DyadicDelayedFork) (t s : DyadicTreeNode) :
    delayedReadAtom (𝕜 := 𝕜) (p := p) (S := S) e t s =
      if t ∈ dyadicRootedCell e.fork s then 1 else 0 := by
  classical
  by_cases h : ∃ u, t ∈ dyadicRootedCell e.fork u
  · rw [delayedReadAtom, dif_pos h, single_apply]
    have hc := Classical.choose_spec h
    by_cases hs : t ∈ dyadicRootedCell e.fork s
    · have heq : Classical.choose h = s := by
        by_contra hne
        exact Finset.disjoint_left.mp (dyadicRootedCell_disjoint e.fork hne) hc hs
      simp [heq, hs]
    · have hne : Classical.choose h ≠ s := fun hcs => hs (hcs ▸ hc)
      simp only [if_neg hne, if_neg hs]
  · rw [delayedReadAtom, dif_neg h, zero_apply]
    exact (if_neg (fun hs => h ⟨s, hs⟩)).symm

def delayedReadLinear (e : DyadicDelayedFork) :
    JamesTreePreSpace 𝕜 p S →ₗ[𝕜] JamesTreePreSpace 𝕜 p S :=
  Finsupp.linearCombination 𝕜 (delayedReadAtom e)

theorem delayedReadLinear_single (e : DyadicDelayedFork) (t : DyadicTreeNode) (c : 𝕜) :
    delayedReadLinear (p := p) (S := S) e (single t c) = c • delayedReadAtom e t := by
  exact Finsupp.linearCombination_single 𝕜 c t

theorem delayedReadLinear_apply (e : DyadicDelayedFork)
    (a : JamesTreePreSpace 𝕜 p S) (s : DyadicTreeNode) :
    delayedReadLinear e a s = ∑ t ∈ dyadicRootedCell e.fork s, a t := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_apply, Finset.sum_const_zero]
  | add a b ha hb =>
    simp only [map_add, add_apply, ha, hb]
    exact Finset.sum_add_distrib.symm
  | single t c =>
    change delayedReadLinear e (single t c) s = ∑ u ∈ dyadicRootedCell e.fork s, single t c u
    rw [delayedReadLinear_single, smul_apply, delayedReadAtom_apply]
    simp [single_apply]

theorem delayedReadLinear_norm_le (e : DyadicDelayedFork)
    (hS : ∀ A, S.allows A → S.allows (dyadicRootedCells e.fork A))
    (a : JamesTreePreSpace 𝕜 p S) : ‖delayedReadLinear e a‖ ≤ ‖a‖ := by
  classical
  apply norm_le
  intro T
  let U : JamesTreeTest S := {
    count := T.count
    segment := fun j => dyadicRootedCells e.fork (T.segment j)
    allowed := fun j => hS _ (T.allowed j)
    disjoint := fun i j hij => dyadicRootedCells_disjoint e.fork (T.disjoint hij) }
  have htest : jamesTreeTestMap 𝕜 p T (coefficients (delayedReadLinear e a)) =
      jamesTreeTestMap 𝕜 p U a.coefficients := by
    ext j
    change (∑ s ∈ T.segment j, delayedReadLinear e a s) =
      ∑ t ∈ (T.segment j).biUnion (dyadicRootedCell e.fork), a t
    simp only [delayedReadLinear_apply]
    exact (Finset.sum_biUnion (fun s _ t _ hst => dyadicRootedCell_disjoint e.fork hst)).symm
  rw [htest]
  exact a.test_norm_le U

def delayedRead (e : DyadicDelayedFork)
    (hS : ∀ A, S.allows A → S.allows (dyadicRootedCells e.fork A)) :
    JamesTreePreSpace 𝕜 p S →L[𝕜] JamesTreePreSpace 𝕜 p S :=
  (delayedReadLinear e).mkContinuous 1 (fun a => by
    simpa only [one_mul] using delayedReadLinear_norm_le e hS a)

theorem norm_delayedRead_le (e : DyadicDelayedFork)
    (hS : ∀ A, S.allows A → S.allows (dyadicRootedCells e.fork A)) :
    ‖delayedRead (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ThesisCommon.JamesTreePreSpace
