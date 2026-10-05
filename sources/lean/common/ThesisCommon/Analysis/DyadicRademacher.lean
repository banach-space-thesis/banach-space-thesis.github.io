import ThesisCommon.Analysis.SchurRademacher
import ThesisCommon.Analysis.LatticeDisjointFinite

/-! Coherent dyadic partitions yield a Rademacher system. This file handles
the finite combinatorics; construction of the fragments is separate. -/
noncomputable section
open scoped BigOperators Topology
namespace ThesisCommon

theorem sum_bool_snoc {E : Type*} [AddCommMonoid E] {n : ℕ}
    (f : (Fin (n+1) → Bool) → E) :
    ∑ ω, f ω = ∑ ω : Fin n → Bool, (f (Fin.snoc ω false) + f (Fin.snoc ω true)) := by
  have heq : (∑ ω, f ω) =
      ∑ q : Bool × (Fin n → Bool), f (Fin.snoc q.2 q.1) :=
    (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)) _ f (fun _ => rfl)).symm
  rw [heq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => add_comm _ _)

section Group
variable {E : Type*} [AddCommGroup E]
variable (p : (n : ℕ) → (Fin n → Bool) → E)
variable (hparent : ∀ n ω, p (n+1) (Fin.snoc ω false) + p (n+1) (Fin.snoc ω true) = p n ω)

def dyadicRademacher (n : ℕ) : E :=
  ∑ ω : Fin (n+1) → Bool, signedValue (ω (Fin.last n)) (p (n+1) ω)

include hparent

theorem dyadic_sum_eq_root (n : ℕ) : ∑ ω : Fin n → Bool, p n ω = p 0 Fin.elim0 := by
  induction n with
  | zero => simp only [Fintype.sum_unique]; rfl
  | succ n ih => rw [sum_bool_snoc]; simp_rw [hparent]; exact ih

theorem dyadicRademacher_reconstruct (n i : ℕ) (hi : i < n) :
    dyadicRademacher p i = ∑ ω : Fin n → Bool, signedValue (ω ⟨i, hi⟩) (p n ω) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : i = n
    · subst i
      rfl
    · have hin : i < n := by omega
      rw [ih hin, sum_bool_snoc]
      apply Finset.sum_congr rfl
      intro ω _
      change signedValue (ω ⟨i, hin⟩) (p n ω) =
        signedValue ((Fin.snoc ω false : Fin (n+1) → Bool) (⟨i, hin⟩ : Fin n).castSucc)
          (p (n+1) (Fin.snoc ω false)) +
        signedValue ((Fin.snoc ω true : Fin (n+1) → Bool) (⟨i, hin⟩ : Fin n).castSucc)
          (p (n+1) (Fin.snoc ω true))
      simp only [Fin.snoc_castSucc]
      rw [← hparent n ω]
      cases ω ⟨i, hin⟩ <;> simp [signedValue, add_comm]

end Group

section Lattice
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
variable (p : (n : ℕ) → (Fin n → Bool) → E)
variable (hparent : ∀ n ω, p (n+1) (Fin.snoc ω false) + p (n+1) (Fin.snoc ω true) = p n ω)
variable (hpos : ∀ n ω, 0 ≤ p n ω)
variable (hdisjoint : ∀ n, Pairwise (fun ω η => p n ω ⊓ p n η = 0))
include hparent hpos hdisjoint

omit [NormedSpace ℝ E] [HasSolidNorm E] in
theorem dyadicRademacher_abs (n : ℕ) : |dyadicRademacher p n| = p 0 Fin.elim0 := by
  have habs (ω : Fin (n+1) → Bool) :
      |signedValue (ω (Fin.last n)) (p (n+1) ω)| = p (n+1) ω := by
    cases ω (Fin.last n) <;> simp [signedValue, abs_of_nonneg (hpos (n+1) ω)]
  rw [dyadicRademacher, lattice_abs_sum_of_pairwise_disjoint]
  · simp_rw [habs]
    exact dyadic_sum_eq_root p hparent (n+1)
  · intro ω _ η _ hne
    rw [habs, habs]
    exact hdisjoint (n+1) hne

theorem dyadicRademacher_norm (n : ℕ) : ‖dyadicRademacher p n‖ = ‖p 0 Fin.elim0‖ := by
  rw [← norm_abs_eq_norm, dyadicRademacher_abs p hparent hpos hdisjoint]

/-- A nonzero coherent, disjoint dyadic partition with uniformly bounded
scaled leaf norms cannot exist in a space isomorphic to ell-one. -/
theorem dyadic_root_eq_zero_of_equiv_ellOne {I : Type*}
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n ω, (Fintype.card (Fin n → Bool) : ℝ) * ‖p n ω‖ ≤ M) :
    p 0 Fin.elim0 = 0 := by
  have ht := schur_rademacher_tendsto_zero d (dyadicRademacher p) p hM hp
    (fun n i => dyadicRademacher_reconstruct p hparent n i i.isLt)
  have hnorm : Filter.Tendsto (fun _ : ℕ => ‖p 0 Fin.elim0‖) Filter.atTop (𝓝 0) := by
    simpa only [dyadicRademacher_norm p hparent hpos hdisjoint, norm_zero] using ht.norm
  exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hnorm)

end Lattice
end ThesisCommon
