import ThesisCommon.Analysis.DyadicRademacher

/-! Actual recursive dyadic partitions from a positive halving operation. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]

def dyadicHalves (split : E → Bool → E) (x : E) : (n : ℕ) → (Fin n → Bool) → E
  | 0, _ => x
  | n+1, ω => split (dyadicHalves split x n (Fin.init ω)) (ω (Fin.last n))

section Halves
variable (x : E) (hx : 0 ≤ x) (split : E → Bool → E)
variable (hpos : ∀ y, 0 ≤ y → y ≤ x → ∀ b, 0 ≤ split y b)
variable (hle : ∀ y, 0 ≤ y → y ≤ x → ∀ b, split y b ≤ y)
variable (hsum : ∀ y, 0 ≤ y → y ≤ x → split y false + split y true = y)
variable (hdisj : ∀ y, 0 ≤ y → y ≤ x → split y false ⊓ split y true = 0)
variable (hnorm : ∀ y, 0 ≤ y → y ≤ x → ∀ b, ‖split y b‖ = ‖y‖ / 2)

include hx hpos hle in
theorem dyadicHalves_bounds (n : ℕ) (ω : Fin n → Bool) :
    0 ≤ dyadicHalves split x n ω ∧ dyadicHalves split x n ω ≤ x := by
  induction n with
  | zero => exact ⟨hx, le_rfl⟩
  | succ n ih =>
    have h := ih (Fin.init ω)
    exact ⟨hpos _ h.1 h.2 _, (hle _ h.1 h.2 _).trans h.2⟩

include hx hpos hle hsum in
theorem dyadicHalves_parent (n : ℕ) (ω : Fin n → Bool) :
    dyadicHalves split x (n+1) (Fin.snoc ω false) +
      dyadicHalves split x (n+1) (Fin.snoc ω true) = dyadicHalves split x n ω := by
  simp only [dyadicHalves, Fin.init_snoc, Fin.snoc_last]
  have h := dyadicHalves_bounds x hx split hpos hle n ω
  exact hsum _ h.1 h.2

include hx hpos hle hdisj in
theorem dyadicHalves_disjoint (n : ℕ) :
    Pairwise (fun ω η => dyadicHalves split x n ω ⊓ dyadicHalves split x n η = 0) := by
  induction n with
  | zero => intro ω η hne; exact False.elim (hne (Subsingleton.elim _ _))
  | succ n ih =>
    intro ω η hne
    have hω := dyadicHalves_bounds x hx split hpos hle n (Fin.init ω)
    have hη := dyadicHalves_bounds x hx split hpos hle n (Fin.init η)
    by_cases hi : Fin.init ω = Fin.init η
    · have hlast : ω (Fin.last n) ≠ η (Fin.last n) := by
        intro heq
        apply hne
        rw [← Fin.snoc_init_self ω, ← Fin.snoc_init_self η, hi, heq]
      simp only [dyadicHalves, hi]
      have h := hdisj _ hη.1 hη.2
      cases hωlast : ω (Fin.last n) <;> cases hηlast : η (Fin.last n)
      · exact False.elim (hlast (hωlast.trans hηlast.symm))
      · exact h
      · simpa only [inf_comm] using h
      · exact False.elim (hlast (hωlast.trans hηlast.symm))
    · apply le_antisymm
      · exact (inf_le_inf (hle _ hω.1 hω.2 _) (hle _ hη.1 hη.2 _)).trans_eq (ih hi)
      · exact le_inf (hpos _ hω.1 hω.2 _) (hpos _ hη.1 hη.2 _)

include hx hpos hle hnorm in
theorem dyadicHalves_scaled_norm (n : ℕ) (ω : Fin n → Bool) :
    (Fintype.card (Fin n → Bool) : ℝ) * ‖dyadicHalves split x n ω‖ = ‖x‖ := by
  induction n with
  | zero => simp [dyadicHalves]
  | succ n ih =>
    have h := dyadicHalves_bounds x hx split hpos hle n (Fin.init ω)
    have hn := hnorm _ h.1 h.2 (ω (Fin.last n))
    have hp := ih (Fin.init ω)
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at *
    change ((2 : ℝ) ^ n * 2) * ‖split (dyadicHalves split x n (Fin.init ω)) (ω (Fin.last n))‖ = ‖x‖
    rw [hn]
    nlinarith

include hx hpos hle hsum hdisj hnorm in
theorem eq_zero_of_dyadic_halving {I : Type*}
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) : x = 0 := by
  have h := dyadic_root_eq_zero_of_equiv_ellOne (dyadicHalves split x)
    (dyadicHalves_parent x hx split hpos hle hsum)
    (fun n ω => (dyadicHalves_bounds x hx split hpos hle n ω).1)
    (dyadicHalves_disjoint x hx split hpos hle hdisj) d (norm_nonneg x)
    (fun n ω => (dyadicHalves_scaled_norm x hx split hpos hle hnorm n ω).le)
  exact h

end Halves
end ThesisCommon
