import JLMS.L1Restriction
import JLMS.ScatteredTopology
import JLMS.FiniteMass

/-!
# Lemma 5.4 and Corollary 5.5: essential weights

This is the full neighborhood and finite-mass argument, in ℓ¹ coordinates.
The sequences need only a common norm bound. The eventual-weight contradiction
is the same one in the paper: separate the first N finite sets simultaneously,
group the neighborhoods, and apply the total mass bound with N ε > M.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

/-- Lemma 5.4, with the dual functionals expressed in atomic coordinates. -/
theorem exists_neighborhood_arbitrarily_late_small_weight (hK : IsScattered K)
    (f : ℕ → ellOneOn 𝕜 K) (F : ℕ → Finset K)
    (hF : Pairwise fun i j => Disjoint (F i) (F j))
    (M : ℝ) (hM : ∀ j, ‖f j‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ U : NeighborhoodFamily (fun k : ↥(F n) => (k : K)),
      ∀ J : ℕ, ∃ j : ℕ, J < j ∧ ‖restrictionL1 (⋃ k, U.sets k) (f j)‖ < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (M / ε)
  have hlarge : M < N * ε := (div_lt_iff₀ hε).mp hN
  let Points := Σ n : Fin N, ↥(F n.val)
  let p : Points → K := fun q => q.2.val
  have hp : Function.Injective p := by
    rintro ⟨n, k⟩ ⟨m, l⟩ hkl
    change k.val = l.val at hkl
    have hnm : n = m := by
      by_contra hne
      have hd := hF (show n.val ≠ m.val from fun h => hne (Fin.ext h))
      exact Finset.disjoint_left.mp hd k.property (hkl.symm ▸ l.property)
    subst m
    have hkl' : k = l := Subtype.ext hkl
    subst l
    rfl
  obtain ⟨W⟩ := exists_neighborhoodFamily hK p hp
  let U (n : Fin N) : NeighborhoodFamily (fun k : ↥(F n.val) => (k : K)) :=
    { sets := fun k => W.sets ⟨n, k⟩
      clopen := fun k => W.clopen ⟨n, k⟩
      compact := fun k => W.compact ⟨n, k⟩
      contains := fun k => W.contains ⟨n, k⟩
      disjoint := by
        intro k l hkl
        exact W.disjoint (by intro h; exact hkl (eq_of_heq (Sigma.mk.inj h).2)) }
  let C (n : Fin N) : Set K := ⋃ k, (U n).sets k
  have hC : Pairwise fun n m => Disjoint (C n) (C m) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hxn hxm
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxn
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hxm
    exact Set.disjoint_left.mp
      (W.disjoint (by intro h; exact hnm (Sigma.mk.inj h).1)) hk hl
  have hbudget (j : ℕ) : ∑ n : Fin N, ‖restrictionL1 (C n) (f j)‖ ≤ M := by
    exact (sum_restrictionL1_norm_le Finset.univ C
      (by intro n _ m _ hnm; exact hC hnm) (f j)).trans (hM j)
  obtain ⟨n, hn⟩ := exists_arbitrarily_late_small_of_sum_le
    (fun n j => ‖restrictionL1 (C n) (f j)‖) M ε hbudget hlarge
  exact ⟨n.val, U n, hn⟩

/-- Corollary 5.5: extract one subsequence on which the neighborhood weight
is uniformly below ε. -/
theorem exists_neighborhood_subsequence_small_weight (hK : IsScattered K)
    (f : ℕ → ellOneOn 𝕜 K) (F : ℕ → Finset K)
    (hF : Pairwise fun i j => Disjoint (F i) (F j))
    (M : ℝ) (hM : ∀ j, ‖f j‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ U : NeighborhoodFamily (fun k : ↥(F n) => (k : K)),
      ∃ s : ℕ → ℕ, StrictMono s ∧
        ∀ j, ‖restrictionL1 (⋃ k, U.sets k) (f (s j))‖ < ε := by
  obtain ⟨n, U, hU⟩ := exists_neighborhood_arbitrarily_late_small_weight hK f F hF M hM hε
  obtain ⟨s, hs, hsmall⟩ := exists_strictMono_of_arbitrarily_late
    (fun j => ‖restrictionL1 (⋃ k, U.sets k) (f j)‖ < ε) hU
  exact ⟨n, U, s, hs, hsmall⟩

end JLMS
