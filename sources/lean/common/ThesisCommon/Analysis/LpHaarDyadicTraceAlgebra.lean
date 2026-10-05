import ThesisCommon.Analysis.LpHaarTraceLimit
import ThesisCommon.Analysis.LpHaarSignedChildIndices

/-! Finite additivity reconstructs traces of finite dyadic parents and
their signed children from the actual atom traces. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (a : LpHaarDyadicSetIndex → 𝕜)
  (hadd : ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
    lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j → a k = a i + a j)
include hadd

theorem lpHaarDyadicTrace_empty (n : ℕ) : a ⟨n, ∅⟩ = 0 := by
  have h := hadd ⟨n, ∅⟩ ⟨n, ∅⟩ ⟨n, ∅⟩
    (by simp [lpHaarDyadicSet, lpHaarBlockParent])
    (by simp [lpHaarDyadicSet, lpHaarBlockParent])
  exact add_eq_left.mp h.symm

theorem lpHaarDyadicTrace_sum_atoms (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    a ⟨n, S⟩ = ∑ k ∈ S, a ⟨n, {k}⟩ := by
  induction S using Finset.induction_on with
  | empty => simpa using lpHaarDyadicTrace_empty a hadd n
  | @insert k S hk ih =>
    have hdis : Disjoint (lpHaarDyadicSet ⟨n, {k}⟩) (lpHaarDyadicSet ⟨n, S⟩) := by
      change Disjoint (lpHaarBlockParent n {k}) (lpHaarBlockParent n S)
      simp only [lpHaarBlockParent, Finset.mem_singleton, iUnion_iUnion_eq_left]
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact lpHaarCell_disjoint_sameLevel n (fun h => hk ((Fin.ext h).symm ▸ hj))
    have hunion : lpHaarDyadicSet ⟨n, insert k S⟩ =
        lpHaarDyadicSet ⟨n, {k}⟩ ∪ lpHaarDyadicSet ⟨n, S⟩ := by
      ext x
      simp [lpHaarDyadicSet, lpHaarBlockParent]
    rw [hadd _ _ _ hdis hunion, ih, Finset.sum_insert hk]

theorem lpHaarDyadicTrace_signed_child (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    a ⟨n + 1, lpHaarSignedChildAtoms n S θ⟩ =
      ∑ k ∈ S, a ⟨n + 1, {lpHaarSignedChildIndex n θ k}⟩ := by
  rw [lpHaarDyadicTrace_sum_atoms a hadd, lpHaarSignedChildAtoms, Finset.sum_map]

theorem lpHaarDyadicTrace_child_pair (n : ℕ) (k : Fin (2 ^ n))
    (θ : Fin (2 ^ n) → Bool) :
    a ⟨n + 1, {lpHaarSignedChildIndex n θ k}⟩ +
      a ⟨n + 1, {lpHaarSignedChildIndex n (fun j => !(θ j)) k}⟩ = a ⟨n, {k}⟩ := by
  apply Eq.symm
  apply hadd
  · change Disjoint (lpHaarBlockParent (n + 1) {lpHaarSignedChildIndex n θ k})
      (lpHaarBlockParent (n + 1) {lpHaarSignedChildIndex n (fun j => !(θ j)) k})
    simp only [lpHaarBlockParent, Finset.mem_singleton, iUnion_iUnion_eq_left]
    exact lpHaarSignedChild_disjoint_complement n k (θ k)
  · change lpHaarBlockParent n {k} =
      lpHaarBlockParent (n + 1) {lpHaarSignedChildIndex n θ k} ∪
        lpHaarBlockParent (n + 1) {lpHaarSignedChildIndex n (fun j => !(θ j)) k}
    simp only [lpHaarBlockParent, Finset.mem_singleton, iUnion_iUnion_eq_left]
    exact (lpHaarSignedChild_union n k (θ k)).symm

end ThesisCommon
