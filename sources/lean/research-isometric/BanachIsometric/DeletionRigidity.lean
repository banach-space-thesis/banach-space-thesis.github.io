import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Rigidity of proportional one-point-deletion spectra

This is the eigenvalue-multiset sublemma in Theorem D. Positivity and
proportionality of all deletion multisets force every eigenvalue to coincide.
The proof does not need an ordering of the eigenvalues: deletion multisets
retaining a common maximum have scaling factor one, so their sums identify all
entries except possibly the chosen maximum. A further deletion identifies it.
This replaces the geometric-progression/condition-number argument in the paper.
-/

namespace BanachIsometric

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full multiset after deleting one index. Repeated values are retained
with their multiplicities, as required for eigenvalue spectra. -/
def deletionMultiset (a : ι → ℝ) (i : ι) : Multiset ℝ :=
  (Finset.univ.erase i).val.map a

@[simp] theorem mem_deletionMultiset (a : ι → ℝ) (i : ι) (x : ℝ) :
    x ∈ deletionMultiset a i ↔ ∃ j, j ≠ i ∧ a j = x := by
  unfold deletionMultiset
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨j, hj, hjx⟩
    exact ⟨j, (Finset.mem_erase.mp hj).1, hjx⟩
  · rintro ⟨j, hji, hjx⟩
    exact ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, hjx⟩

theorem sum_deletionMultiset_add (a : ι → ℝ) (i : ι) :
    (deletionMultiset a i).sum + a i = ∑ j, a j := by
  exact Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)

private theorem scale_eq_one_of_common_positive_max
    (s t : Multiset ℝ) {c M : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hMs : M ∈ s) (hMt : M ∈ t)
    (hs : ∀ x ∈ s, x ≤ M) (ht : ∀ x ∈ t, x ≤ M)
    (heq : s = t.map (fun x => c * x)) : c = 1 := by
  have hscaled : c * M ∈ s := by
    rw [heq]
    exact Multiset.mem_map_of_mem _ hMt
  have hle : c * M ≤ M := hs _ hscaled
  have hMmap : M ∈ t.map (fun x => c * x) := by rwa [← heq]
  obtain ⟨x, hx, hcx⟩ := Multiset.mem_map.mp hMmap
  have hge : M ≤ c * M := by
    calc
      M = c * x := hcx.symm
      _ ≤ c * M := mul_le_mul_of_nonneg_left (ht x hx) hc.le
  nlinarith

/-- The genuine finite-spectrum rigidity assertion used in Theorem D.
All one-index-deletion *multisets* are positively proportional. Their order is
irrelevant, and duplicate entries have their original multiplicities. -/
theorem positive_deletion_multisets_rigid
    (hcard : 3 ≤ Fintype.card ι) (a : ι → ℝ) (hpos : ∀ i, 0 < a i)
    (hprop : ∀ i j, ∃ c : ℝ, 0 < c ∧
      deletionMultiset a i = (deletionMultiset a j).map (fun x => c * x)) :
    ∀ i j, a i = a j := by
  classical
  obtain ⟨r, s, t, hrs, hrt, hst⟩ :=
    Fintype.two_lt_card_iff.mp (show 2 < Fintype.card ι by omega)
  have hnonempty : (Finset.univ : Finset ι).Nonempty := ⟨r, Finset.mem_univ r⟩
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ a hnonempty
  have hmax (i : ι) : a i ≤ a m := hm i (Finset.mem_univ i)
  have htwo : ∃ i j : ι, i ≠ m ∧ j ≠ m ∧ i ≠ j := by
    by_cases hrm : r = m
    · subst r
      exact ⟨s, t, hrs.symm, hrt.symm, hst⟩
    by_cases hsm : s = m
    · subst s
      exact ⟨r, t, hrs, hst.symm, hrt⟩
    exact ⟨r, s, hrm, hsm, hrs⟩
  obtain ⟨i, j, him, hjm, hij⟩ := htwo
  have hsame (k : ι) (hkm : k ≠ m) : a k = a i := by
    obtain ⟨c, hc, heq⟩ := hprop k i
    have hc1 : c = 1 := scale_eq_one_of_common_positive_max
      (deletionMultiset a k) (deletionMultiset a i) hc (hpos m)
      ((mem_deletionMultiset a k (a m)).mpr ⟨m, hkm.symm, rfl⟩)
      ((mem_deletionMultiset a i (a m)).mpr ⟨m, him.symm, rfl⟩)
      (fun x hx => by
        obtain ⟨l, _, rfl⟩ := (mem_deletionMultiset a k x).mp hx
        exact hmax l)
      (fun x hx => by
        obtain ⟨l, _, rfl⟩ := (mem_deletionMultiset a i x).mp hx
        exact hmax l) heq
    have hdel : deletionMultiset a k = deletionMultiset a i := by
      simpa only [hc1, one_mul, Multiset.map_id'] using heq
    have hsums := congrArg Multiset.sum hdel
    linarith [sum_deletionMultiset_add a k, sum_deletionMultiset_add a i]
  have hall (x : ℝ) (hx : x ∈ deletionMultiset a m) : x = a i := by
    obtain ⟨k, hkm, rfl⟩ := (mem_deletionMultiset a m x).mp hx
    exact hsame k hkm
  obtain ⟨c, hc, heq⟩ := hprop m i
  have hscaled (k : ι) (hki : k ≠ i) : c * a k = a i := by
    apply hall
    rw [heq]
    exact Multiset.mem_map_of_mem _
      ((mem_deletionMultiset a i (a k)).mpr ⟨k, hki, rfl⟩)
  have hmi : a m = a i := by
    have hm' := hscaled m him.symm
    have hj' := hscaled j hij.symm
    rw [hsame j hjm] at hj'
    nlinarith
  have hconst (k : ι) : a k = a i := by
    by_cases hkm : k = m
    · simpa only [hkm] using hmi
    · exact hsame k hkm
  exact fun k l => (hconst k).trans (hconst l).symm

/-- The paper's list of `n+1` positive eigenvalues, for `n ≥ 2`. No ordering
assumption is necessary for this multiset formulation. -/
theorem positive_eigenvalue_deletions_constant {n : ℕ} (hn : 2 ≤ n)
    (a : Fin (n + 1) → ℝ) (hpos : ∀ i, 0 < a i)
    (hprop : ∀ i j, ∃ c : ℝ, 0 < c ∧
      deletionMultiset a i = (deletionMultiset a j).map (fun x => c * x)) :
    ∃ L : ℝ, 0 < L ∧ ∀ i, a i = L := by
  have hcard : 3 ≤ Fintype.card (Fin (n + 1)) := by simpa using (show 3 ≤ n + 1 by omega)
  have hrigid := positive_deletion_multisets_rigid hcard a hpos hprop
  exact ⟨a 0, hpos 0, fun i => hrigid i 0⟩

end BanachIsometric
