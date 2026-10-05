import LPCK.OrdinalDualCotype
import LPCK.MainStatements
import JLMS.OrdinalSpacePowerReduction
import JLMS.OrdinalSpaceFinitePower
import JLMS.OrdinalSpaceInitialFiniteReduction
import ThesisCommon.Analysis.LpFiniteProducts
import ThesisCommon.Analysis.FiniteCompactPrimariness
import ThesisCommon.Analysis.FiniteOrdinalCoefficients

/-! The complete ordinal sequence assembly on the actual spaces. Its sole
remaining analytic input is UPFP of C[0,omega^gamma] for every nonzero gamma.
This input is explicit and this file is not counted as the original main proof. -/
noncomputable section
namespace LPCK
open ThesisCommon
open scoped ENNReal
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

theorem canonicalOrdinal_sequence_of_base (γ : Ordinal.{u}) (hγ : γ ≠ 0)
    (hbase : HasUPFP 𝕜 (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ)))
    (p : BanachExponent) : Theorem_1_1 𝕜 (Ordinal.omega0 ^ γ) p := by
  have hD : ordinalDerived (Set.Icc 0 (Ordinal.omega0 ^ γ)) γ = {Ordinal.omega0 ^ γ} := by
    have hI : Set.Icc (0 : Ordinal.{u}) (Ordinal.omega0 ^ γ) =
        Set.Iic (Ordinal.omega0 ^ γ) := by ext x; simp
    rw [hI]
    exact ordinalDerived_Iic_power_self hγ
  have hsum : HasUPFP 𝕜 (SequenceSum p (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ))) := by
    by_cases hpTop : p.val = ∞
    · have hp : p = ⟨∞, by simp⟩ := Subtype.ext hpTop
      subst p
      exact hbase.ordinal_infinity hD
    by_cases hpOne : p.val = 1
    · have hp : p = ⟨1, le_rfl⟩ := Subtype.ext hpOne
      subst p
      exact ordinal_ellOne_hasUPFP_of_base _ hbase
    have hreal : 1 < p.val.toReal := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal (by simp) hpTop).mpr
          (lt_of_le_of_ne p.property (Ne.symm hpOne))
    exact (ordinal_lp_finite_upfp_primary_of_dual_equiv_ellOne hD hpTop hreal hbase
      (ordinalContinuousDualEllOneEquiv _)).1
  exact ⟨hsum, hsum.lp_isPrimary⟩

def ordinalFiniteMultipleLpEquiv (α : Ordinal.{u})
    (hα : Ordinal.omega0 ≤ α) (n : ℕ) (p : BanachExponent) :
    SequenceSum p (OrdinalContinuous 𝕜 (α * ((n + 1 : ℕ) : Ordinal))) ≃L[𝕜]
      SequenceSum p (OrdinalContinuous 𝕜 α) :=
  (lpMapEquiv p.val (JLMS.ordinalSpaceFinitePower (𝕜 := 𝕜) α hα n)).trans
    (lpCountableFinitePiCoefficientEquiv (𝕜 := 𝕜) (κ := Fin (n + 1)) p.val)

theorem exists_ordinal_sequence_canonical_power (α : Ordinal.{u})
    (hα : Ordinal.omega0 ≤ α) (p : BanachExponent) :
    ∃ γ : Ordinal.{u}, γ ≠ 0 ∧ Nonempty
      (SequenceSum p (OrdinalContinuous 𝕜 α) ≃L[𝕜]
        SequenceSum p (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ))) := by
  have hωsquare : (Cardinal.aleph0 : Cardinal.{u}).ord ^ (2 : Ordinal.{u}) =
      Ordinal.omega0 * Ordinal.omega0 := by
    rw [Cardinal.ord_aleph0, ← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
  by_cases hsmall : α < Ordinal.omega0 * Ordinal.omega0
  · obtain ⟨n, ρ, hρ, he⟩ := JLMS.exists_initial_finite_quotient_remainder
      (Cardinal.aleph0 : Cardinal.{u}) le_rfl α (by simpa using hα) (by simpa using hsmall)
    have hmul : (Cardinal.aleph0 : Cardinal.{u}).ord ≤
        (Cardinal.aleph0 : Cardinal.{u}).ord * ((n + 1 : ℕ) : Ordinal) := by
      calc
        _ = (Cardinal.aleph0 : Cardinal.{u}).ord * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) _
    let e := (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
      (JLMS.ordinalSpaceSmallRemainder (Cardinal.aleph0 : Cardinal.{u}) le_rfl _ ρ hmul hρ)
    refine ⟨1, by simp, ⟨?_⟩⟩
    have e' : OrdinalContinuous 𝕜 α ≃L[𝕜]
        OrdinalContinuous 𝕜 (Ordinal.omega0 * ((n + 1 : ℕ) : Ordinal)) := by
      rw [Cardinal.ord_aleph0] at e
      exact e
    rw [Ordinal.opow_one]
    exact (lpMapEquiv p.val e').trans (ordinalFiniteMultipleLpEquiv _ le_rfl n p)
  · obtain ⟨γ, hγ, η, hη, hηω, ⟨e⟩⟩ :=
      JLMS.exists_ordinalSpace_power_normalForm (𝕜 := 𝕜)
        (Cardinal.aleph0 : Cardinal.{u}) le_rfl α (by rw [hωsquare]; exact le_of_not_gt hsmall)
    have hηlt : η < Ordinal.omega0 := by simpa only [Cardinal.ord_aleph0] using hηω
    obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hηlt
    have hmpos : 0 < m := by rw [hm] at hη; exact_mod_cast hη
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
    have hωpow : Ordinal.omega0 ≤ Ordinal.omega0 ^ γ := by
      simpa only [Ordinal.opow_one] using
        (Ordinal.opow_le_opow_right Ordinal.omega0_pos (one_le_two.trans hγ))
    refine ⟨γ, (zero_lt_one.trans_le (one_le_two.trans hγ)).ne', ⟨?_⟩⟩
    have e' : OrdinalContinuous 𝕜 α ≃L[𝕜]
        OrdinalContinuous 𝕜 ((Ordinal.omega0 ^ γ) * ((n + 1 : ℕ) : Ordinal)) := by
      rw [Cardinal.ord_aleph0, hm, hn, Nat.succ_eq_add_one] at e
      exact e
    exact (lpMapEquiv p.val e').trans (ordinalFiniteMultipleLpEquiv _ hωpow n p)

theorem theorem_1_1_of_canonical_bases
    (hbases : ∀ γ : Ordinal.{u}, γ ≠ 0 →
      HasUPFP 𝕜 (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ)))
    (α : Ordinal.{u}) (p : BanachExponent) : Theorem_1_1 𝕜 α p := by
  by_cases hfinite : α < Ordinal.omega0
  · letI := ordinalInterval_finite hfinite
    exact finiteCompact_lp_upfp_primary (OrdinalInterval α) p.val
  obtain ⟨γ, hγ, ⟨e⟩⟩ := exists_ordinal_sequence_canonical_power (𝕜 := 𝕜)
    α (le_of_not_gt hfinite) p
  have h := (canonicalOrdinal_sequence_of_base γ hγ (hbases γ hγ) p).1.of_equiv e.symm
  exact ⟨h, h.lp_isPrimary⟩

end LPCK
