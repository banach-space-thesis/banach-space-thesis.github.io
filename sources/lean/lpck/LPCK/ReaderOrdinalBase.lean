import LPCK.AllOrdinalTheorem

noncomputable section
universe u

namespace LPCK
open JLMS ThesisCommon

variable {𝕜 : Type} [RCLike 𝕜]

set_option synthInstance.maxSize 8192 in
/-- Theorem 2.10 for infinite ordinal intervals, using the ordinal models
already used to prove the sequence-space theorem. -/
theorem theorem_2_10_infinite (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α)
    (hexcluded : ∀ c : Cardinal.{u}, c.IsRegular → Cardinal.aleph0 < c →
      ∀ n : ℕ, 2 ≤ n →
        ¬ Nonempty (OrdinalContinuous 𝕜 α ≃L[𝕜] OrdinalContinuous 𝕜 (c.ord * n))) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) := by
  let c := α.card
  by_cases hc : c ≤ Cardinal.aleph0
  · have hlt : α < (Cardinal.aleph 1).ord := by
      apply Cardinal.lt_ord.mpr
      rw [← Cardinal.succ_aleph0]
      exact Order.lt_succ_iff.mpr hc
    obtain ⟨β, hcβ, hβ, ⟨e⟩⟩ := exists_countableOrdinal_small_infinite_model hlt hα
    exact (Posets.countableOrdinal_hasUPFP (𝕜 := 𝕜) β hcβ hβ).of_equiv
      (continuousMapHomeomorphEquiv e.symm)
  have hu : Cardinal.aleph0 < c := lt_of_not_ge hc
  have hlo : c.ord ≤ α := Cardinal.ord_card_le α
  by_cases hsq : α < c.ord * c.ord
  · by_cases hreg : c.IsRegular
    · by_cases hsmall : α < c.ord * Ordinal.omega0
      · obtain ⟨n, ρ, hρ, heq⟩ := exists_initial_finite_quotient_remainder c hu.le α hlo hsmall
        have hmul : c.ord ≤ c.ord * ((n + 1 : ℕ) : Ordinal) := by
          calc
            c.ord = c.ord * 1 := (mul_one _).symm
            _ ≤ _ := mul_le_mul_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) _
        have e : OrdinalContinuous 𝕜 α ≃L[𝕜]
            OrdinalContinuous 𝕜 (c.ord * ((n + 1 : ℕ) : Ordinal)) :=
          (ordinalSpaceCongrIsometry (𝕜 := 𝕜) heq).toContinuousLinearEquiv.trans
          (ordinalSpaceSmallRemainder c hu.le _ ρ hmul hρ)
        by_cases hn : n = 0
        · subst n
          have hq : c.ord * ((0 + 1 : ℕ) : Ordinal.{u}) = c.ord := by
            rw [Nat.zero_add, Nat.cast_one, mul_one]
          rw [hq] at e
          exact (GenericOrdinal.initialOrdinal_hasUPFP hreg hu).of_equiv e.symm
        · exact (hexcluded c hreg hu (n + 1)
            (Nat.succ_le_succ (Nat.one_le_iff_ne_zero.mpr hn)) ⟨e⟩).elim
      · letI := GenericOrdinal.initialOrdinalInfiniteQuotient_index_infinite hu
          (le_of_not_gt hsmall)
        exact GenericOrdinal.initialOrdinalInfiniteQuotient_hasUPFP_of_scalar
          hreg hu (le_of_not_gt hsmall) hsq (GenericOrdinal.jlmsScalarCZero_infinite_hasUPFP _)
    · exact GenericOrdinal.singularInitialBelowSquare_hasUPFP hu.le hreg hlo hsq.le
  · apply ordinal_above_initial_square_hasUPFP_allUniverses c hu α le_rfl
    have he : c.ord ^ (2 : Ordinal.{u}) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    rw [he]
    exact le_of_not_gt hsq

end LPCK
