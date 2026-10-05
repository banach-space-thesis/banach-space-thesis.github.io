import Posets.OrdinalIdealTransportSmallQuotient
import Posets.OrdinalIdealTransportAssembly
import JLMS.OrdinalSpaceInitialFiniteReduction

/-! Complete finite-quotient transport for Proposition 3.1, and the exact
remaining scalar input for the interval below the square of a regular
uncountable initial ordinal. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- Remainders below the initial ordinal do not affect the ideal statement. -/
theorem proposition_3_1_regular_finiteQuotient
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{0}} (hlo : c.ord ≤ α) (hhi : α < c.ord * Ordinal.omega0) :
    Proposition_3_1 𝕜 α := by
  apply proposition_3_1_of_nonexceptional_hasPFP
  intro hexcl
  obtain ⟨n, ρ, hρ, hα⟩ := exists_initial_finite_quotient_remainder c hu.le α hlo hhi
  have hmul : c.ord ≤ c.ord * ((n + 1 : ℕ) : Ordinal) := by
    calc
      c.ord = c.ord * 1 := (mul_one _).symm
      _ ≤ c.ord * ((n + 1 : ℕ) : Ordinal) :=
        mul_le_mul_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) _
  let e : OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 (c.ord * ((n + 1 : ℕ) : Ordinal)) :=
    (ordinalSpaceCongrIsometry (𝕜 := 𝕜) hα).toContinuousLinearEquiv.trans
      (ordinalSpaceSmallRemainder c hu.le _ ρ hmul hρ)
  by_cases hn : n = 0
  · subst n
    have heq : c.ord * ((0 + 1 : ℕ) : Ordinal) = c.ord := by norm_num
    have e' : OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 c.ord := by rw [heq] at e; exact e
    exact ((initialOrdinal_hasUPFP (𝕜 := 𝕜) hc hu).of_equiv e'.symm).hasPFP
  · exact (hexcl c hu hc (n+1) (by omega) ⟨e⟩).elim

/-- The analytic block argument reduces the infinite-quotient interval to
scalar c₀ operators on infinite sets strictly smaller than the base. -/
theorem proposition_3_1_regular_belowSquare_of_scalar
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (hs : ∀ I : Type, Infinite I → Cardinal.mk I < c →
      HasUPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)))
    {α : Ordinal.{0}} (hlo : c.ord ≤ α) (hhi : α < c.ord * c.ord) :
    Proposition_3_1 𝕜 α := by
  by_cases hω : α < c.ord * Ordinal.omega0
  · exact proposition_3_1_regular_finiteQuotient hc hu hlo hω
  · have hω' := le_of_not_gt hω
    have hinf := initialOrdinalInfiniteQuotient_index_infinite hu hω'
    have hsmall := initialOrdinalInfiniteQuotient_index_small hu hhi
    have hpfp := initialOrdinalInfiniteQuotient_hasUPFP_of_scalar hc hu hω' hhi
      (hs _ hinf hsmall)
    intro _
    letI : Nonempty (Set.Icc (0 : Ordinal.{0}) α) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
    have h := uniqueMaximal_of_hasPFP hpfp.hasPFP
    exact ⟨h.2, fun _ => h.1⟩

end Posets
