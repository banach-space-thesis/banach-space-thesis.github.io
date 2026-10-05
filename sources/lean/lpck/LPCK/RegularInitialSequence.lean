import LPCK.OrdinalDualCotype
import LPCK.MainStatements
import LPCK.GenericOrdinalQuantitative
import Posets.OrdinalClosedCopyInitialPowers
import JLMS.OrdinalSpaceFinitePower
import JLMS.OrdinalSpaceInitialFiniteReduction
import ThesisCommon.Analysis.LpFiniteProducts

/-! Actual sequence spaces on regular uncountable initial intervals and
their finite multiples. Finite repetitions disappear under every outer
sequence norm, including p=1 and p=infinity. -/
noncomputable section
universe u
namespace LPCK
open ThesisCommon
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1200000

theorem theorem_1_1_regular_initial (c : Cardinal.{u})
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (p : BanachExponent) :
    Theorem_1_1 𝕜 c.ord p := by
  have hbase : HasUPFP 𝕜 (OrdinalContinuous 𝕜 c.ord) := LPCK.GenericOrdinal.initialOrdinal_hasUPFP hc hu
  have hD : ordinalDerived (Set.Icc 0 c.ord) c.ord = {c.ord} := by
    have he : Ordinal.omega0 ^ c.ord = c.ord := Posets.ordinal_uncountable_initial_omega_power hu
    have hI : Set.Icc (0 : Ordinal.{u}) c.ord = Set.Iic c.ord := by ext x; simp
    rw [hI]
    have h := ordinalDerived_Iic_power_self
      ((Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hu.le)).ne')
    simpa only [he] using h
  have hsum : HasUPFP 𝕜 (SequenceSum p (OrdinalContinuous 𝕜 c.ord)) := by
    by_cases hpTop : p.val = ∞
    · have hp : p = ⟨∞, by simp⟩ := Subtype.ext hpTop
      subst p
      exact hbase.ordinal_infinity hD
    by_cases hpOne : p.val = 1
    · have hp : p = ⟨1, le_rfl⟩ := Subtype.ext hpOne
      subst p
      exact ordinal_ellOne_hasUPFP_of_base c.ord hbase
    have hreal : 1 < p.val.toReal := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal (by simp) hpTop).mpr
          (lt_of_le_of_ne p.property (Ne.symm hpOne))
    exact (ordinal_lp_finite_upfp_primary_of_dual_equiv_ellOne hD hpTop hreal hbase
      (ordinalContinuousDualEllOneEquiv c.ord)).1
  exact ⟨hsum, hsum.lp_isPrimary⟩

def ordinalFiniteMultipleSequenceEquiv (α : Ordinal)
    (hα : Ordinal.omega0 ≤ α) (n : ℕ) (p : BanachExponent) :
    SequenceSum p (OrdinalContinuous 𝕜 (α * ((n + 1 : ℕ) : Ordinal))) ≃L[𝕜]
      SequenceSum p (OrdinalContinuous 𝕜 α) :=
  (lpMapEquiv p.val (JLMS.ordinalSpaceFinitePower (𝕜 := 𝕜) α hα n)).trans
    (lpCountableFinitePiCoefficientEquiv (𝕜 := 𝕜) (κ := Fin (n + 1)) p.val)

theorem theorem_1_1_regular_initial_finite_multiple (c : Cardinal.{u})
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (n : ℕ) (p : BanachExponent) :
    Theorem_1_1 𝕜 (c.ord * ((n + 1 : ℕ) : Ordinal)) p := by
  have h := (theorem_1_1_regular_initial (𝕜 := 𝕜) c hc hu p).1.of_equiv
    (ordinalFiniteMultipleSequenceEquiv c.ord (Cardinal.omega0_le_ord.mpr hu.le) n p).symm
  exact ⟨h, h.lp_isPrimary⟩

theorem theorem_1_1_regular_initial_below_omega_multiple (c : Cardinal.{u})
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (α : Ordinal.{u})
    (hlo : c.ord ≤ α) (hhi : α < c.ord * Ordinal.omega0) (p : BanachExponent) :
    Theorem_1_1 𝕜 α p := by
  obtain ⟨n, ρ, hρ, hα⟩ := JLMS.exists_initial_finite_quotient_remainder c hu.le α hlo hhi
  have hmul : c.ord ≤ c.ord * ((n + 1 : ℕ) : Ordinal) := by
    calc
      c.ord = c.ord * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) _
  let e := (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) hα).toContinuousLinearEquiv.trans
    (JLMS.ordinalSpaceSmallRemainder c hu.le (c.ord * ((n + 1 : ℕ) : Ordinal)) ρ hmul hρ)
  have h := (theorem_1_1_regular_initial_finite_multiple (𝕜 := 𝕜) c hc hu n p).1.of_equiv
    (lpMapEquiv p.val e.symm)
  exact ⟨h, h.lp_isPrimary⟩

end LPCK
