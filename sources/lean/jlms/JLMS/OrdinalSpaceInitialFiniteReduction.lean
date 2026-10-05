import JLMS.OrdinalSpaceAbsorption
import JLMS.OrdinalSpaceReduction

/-!
# The finite-quotient initial-ordinal branch of the classification reduction

If κ is regular uncountable and κ≤α<κω, ordinal division writes
α=κ(n+1)+ρ with ρ<κ. The small remainder is absorbed by an actual
continuous linear equivalence, giving the finite-power branch of Section 9.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_initial_finite_quotient_remainder (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (α : Ordinal.{u})
    (hlo : c.ord ≤ α) (hhi : α < c.ord * Ordinal.omega0) :
    ∃ n : ℕ, ∃ ρ < c.ord, α = c.ord * ((n + 1 : ℕ) : Ordinal) + ρ := by
  have hκ : (0 : Ordinal) < c.ord := by
    exact Ordinal.omega0_pos.trans_le (by simpa using Cardinal.ord_le_ord.mpr hc)
  have hdiv : α / c.ord < Ordinal.omega0 := (Ordinal.div_lt hκ.ne').mpr hhi
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hdiv
  have hmpos : 0 < m := by
    have hpos := (Ordinal.div_pos hκ.ne').mpr hlo
    rw [hm] at hpos
    exact_mod_cast hpos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  refine ⟨n, α % c.ord, Ordinal.mod_lt _ hκ.ne', ?_⟩
  have hd := (Ordinal.div_add_mod α c.ord).symm
  simpa only [hm, hn, Nat.succ_eq_add_one] using hd

theorem ordinalSpaceReduction_of_initial_finiteQuotient
    (c : Cardinal.{u}) (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (α : Ordinal.{u}) (hlo : c.ord ≤ α) (hhi : α < c.ord * Ordinal.omega0) :
    OrdinalSpaceReduction 𝕜 α := by
  obtain ⟨n, ρ, hρ, hα⟩ := exists_initial_finite_quotient_remainder c hu.le α hlo hhi
  have hmul : c.ord ≤ c.ord * ((n + 1 : ℕ) : Ordinal) := by
    calc
      c.ord = c.ord * 1 := (mul_one _).symm
      _ ≤ c.ord * ((n + 1 : ℕ) : Ordinal) :=
        mul_le_mul_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) _
  refine Or.inr (Or.inr ⟨c, hc, hu, n, ?_⟩)
  exact ⟨(ordinalSpaceCongrIsometry (𝕜 := 𝕜) hα).toContinuousLinearEquiv.trans
    (ordinalSpaceSmallRemainder c hu.le (c.ord * ((n + 1 : ℕ) : Ordinal)) ρ hmul hρ)⟩

end JLMS
