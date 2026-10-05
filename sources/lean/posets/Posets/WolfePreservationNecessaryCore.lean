import Posets.WolfeNorming
import JLMS.EssentialWeight
import ThesisCommon.Analysis.OrdinalFiniteCover

/-! A rank-preserving form of the essential-weight selection step. A finite
closed cover replaces the ordinary infinite-subsequence pigeonhole argument.
The selected parameter set retains its entire Cantor--Bendixson rank. -/

noncomputable section
open Set Filter Topology ThesisCommon
universe u
namespace Posets
variable {𝕜 K Y : Type*} [RCLike 𝕜] [TopologicalSpace K]
    [LocallyCompactSpace K] [T2Space K] [TopologicalSpace Y] [T1Space Y]

theorem wolfe_exists_closed_core_small_mass
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : Y → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {A : Set Y} (hA : IsClosed A) (α : Ordinal.{u})
    (hα : (ordinalDerived A α).Nonempty)
    {N : ℕ} (U : Fin N → Set K) (hU : ∀ i, IsOpen (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    {C ε : ℝ} (hbound : ∀ x ∈ A, ‖WeakDual.toStrongDual (μ x)‖ ≤ C)
    (hlarge : C < N * ε) :
    ∃ i : Fin N, ∃ B : Set Y, IsClosed B ∧ B ⊆ A ∧
      (ordinalDerived B α).Nonempty ∧ ∀ x ∈ B, wolfeMass M (μ x) (U i) ≤ ε := by
  classical
  let B (i : Fin N) : Set Y := A ∩ {x | wolfeMass M (μ x) (U i) ≤ ε}
  have hclosed (i : Fin N) : IsClosed (B i) := by
    apply hA.inter
    have h := ((isOpen_wolfeMass_gt M hK (hU i) ε).preimage hμ).isClosed_compl
    convert h using 1
    ext x
    simp
  have hcover : A = ⋃ i, B i := by
    apply Subset.antisymm
    · intro x hx
      have hsum : ∑ i : Fin N, wolfeMass M (μ x) (U i) ≤ C :=
        (wolfeMass_finset_sum_le M (μ x) U hdisj Finset.univ).trans (hbound x hx)
      have hex : ∃ i, wolfeMass M (μ x) (U i) ≤ ε := by
        by_contra hn
        push_neg at hn
        have hle : (N : ℝ) * ε ≤ ∑ i : Fin N, wolfeMass M (μ x) (U i) := by
          simpa using (Finset.sum_le_sum (s := Finset.univ)
            (f := fun _ : Fin N => ε) (g := fun i => wolfeMass M (μ x) (U i))
            (fun i _ => (hn i).le))
        linarith
      obtain ⟨i, hi⟩ := hex
      exact mem_iUnion.mpr ⟨i, hx, hi⟩
    · exact iUnion_subset fun i => inter_subset_left
  obtain ⟨x, hx⟩ := hα
  rw [hcover, ordinalDerived_iUnion_finite B hclosed] at hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact ⟨i, B i, hclosed i, inter_subset_left, ⟨x, hi⟩, fun x hx => hx.2⟩

theorem wolfe_exists_neighborhood_closed_core_small_mass
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : Y → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {A : Set Y} (hA : IsClosed A) (α : Ordinal.{u})
    (hα : (ordinalDerived A α).Nonempty)
    (F : ℕ → Finset K) (hF : Pairwise (fun i j => Disjoint (F i) (F j)))
    {C ε : ℝ} (hbound : ∀ x ∈ A, ‖WeakDual.toStrongDual (μ x)‖ ≤ C)
    (hε : 0 < ε) :
    ∃ n : ℕ, ∃ U : JLMS.NeighborhoodFamily (fun k : ↥(F n) => (k : K)),
      ∃ B : Set Y, IsClosed B ∧ B ⊆ A ∧ (ordinalDerived B α).Nonempty ∧
        ∀ x ∈ B, wolfeMass M (μ x) (⋃ k, U.sets k) ≤ ε := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have hlarge : C < N * ε := (div_lt_iff₀ hε).mp hN
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
  obtain ⟨W⟩ := JLMS.exists_neighborhoodFamily hK p hp
  let U (n : Fin N) : JLMS.NeighborhoodFamily (fun k : ↥(F n.val) => (k : K)) :=
    { sets := fun k => W.sets ⟨n, k⟩
      clopen := fun k => W.clopen ⟨n, k⟩
      compact := fun k => W.compact ⟨n, k⟩
      contains := fun k => W.contains ⟨n, k⟩
      disjoint := by
        intro k l hkl
        exact W.disjoint (by intro h; exact hkl (eq_of_heq (Sigma.mk.inj h).2)) }
  let V (n : Fin N) : Set K := ⋃ k, (U n).sets k
  have hV : Pairwise (fun n m => Disjoint (V n) (V m)) := by
    intro n m hnm
    apply disjoint_left.mpr
    intro x hxn hxm
    obtain ⟨k, hk⟩ := mem_iUnion.mp hxn
    obtain ⟨l, hl⟩ := mem_iUnion.mp hxm
    exact disjoint_left.mp (W.disjoint (by intro h; exact hnm (Sigma.mk.inj h).1)) hk hl
  obtain ⟨n, B, hB, hBA, hBα, hsmall⟩ := wolfe_exists_closed_core_small_mass M hK μ hμ hA
    α hα V (fun n => isOpen_iUnion (fun k => ((U n).clopen k).isOpen)) hV hbound hlarge
  exact ⟨n.val, U n, B, hB, hBA, hBα, hsmall⟩

end Posets
