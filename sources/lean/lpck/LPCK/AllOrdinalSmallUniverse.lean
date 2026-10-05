import LPCK.CanonicalOrdinalSequence
import Posets.OrdinalPrincipalUncountablePreservation
import Posets.OrdinalFixedExponentMiddle
import Posets.OrdinalIdealTransportBelowOmegaPower
import Posets.CountableOrdinalUPFPCanonical
import ThesisCommon.Analysis.LpSemilinearIsometry
import ThesisCommon.Analysis.ScalarFactorizationTransport

/-! Unconditional original ordinal theorem in universe zero. The target
also permits larger ordinal universes; the remaining generic block-sum
extensions are kept separate from this proved standard-universe theorem. -/
noncomputable section
namespace LPCK
open ThesisCommon
section SmallScalar
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1800000

theorem initialCanonical_base_hasUPFP (c : Cardinal.{0})
    (hu : Cardinal.aleph0 < c) (g : Ordinal.{0}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (hgc : g = 2 ∨ (Ordinal.omega0 ≤ g ∧ Ordinal.Principal (· + ·) g)) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ g)) := by
  rcases hgc with rfl | ⟨hgω, hgP⟩
  · have he : c.ord ^ (2 : Ordinal.{0}) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    apply Posets.initialHigherBelowOmega_hasUPFP hu
    · exact he.ge
    · exact (Ordinal.opow_lt_opow_iff_right
        (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hu.le))).mpr
        (Ordinal.nat_lt_omega0 2)
  · have hP : Ordinal.Principal (· + ·) (c.ord * g) :=
      Ordinal.principal_add_mul_of_principal_add c.ord
        (Ordinal.one_lt_omega0.trans_le hgω).ne' hgP
    have hωκ : Ordinal.omega0 < c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hu
    have hω : Ordinal.omega0 < c.ord * g :=
      hωκ.trans_le (Ordinal.le_mul_left _ (Ordinal.omega0_pos.trans_le hgω))
    exact (Posets.ordinalPrincipal_hasUPFP (𝕜 := 𝕜) (c.ord * g) hP hω).of_equiv
      (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜)
        (Posets.ordinal_uncountable_initial_power_rank hu g)).toContinuousLinearEquiv

theorem ordinal_above_initial_square_hasUPFP (c : Cardinal.{0})
    (hu : Cardinal.aleph0 < c) (α : Ordinal.{0}) (hcard : α.card ≤ c)
    (hα : c.ord ^ (2 : Ordinal.{0}) ≤ α) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) := by
  obtain ⟨g, hg, hgcard, hgc, ⟨e⟩⟩ :=
    Posets.exists_ordinalSpace_canonical_power_normalForm (𝕜 := 𝕜) c hu.le α hcard hα
  exact (initialCanonical_base_hasUPFP c hu g hg hgcard hgc).of_equiv e.symm

theorem omegaPower_base_hasUPFP_small (γ : Ordinal.{0}) (hγ : γ ≠ 0) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ)) := by
  let α := Ordinal.omega0 ^ γ
  let c := α.card
  have hα : Ordinal.omega0 ≤ α := by
    simpa only [Ordinal.opow_one] using
      (Ordinal.opow_le_opow_right Ordinal.omega0_pos (Ordinal.one_le_iff_ne_zero.mpr hγ))
  by_cases hc : c ≤ Cardinal.aleph0
  · exact Posets.countableOrdinal_hasUPFP α hc hα
  have hu : Cardinal.aleph0 < c := lt_of_not_ge hc
  have hlo : c.ord ≤ α := Cardinal.ord_card_le α
  by_cases hsq : α < c.ord * c.ord
  · by_cases hreg : c.IsRegular
    · by_cases hsmall : α < c.ord * Ordinal.omega0
      · have he : α = c.ord := by
          apply le_antisymm _ hlo
          by_contra hn
          have hκlt : c.ord < α := lt_of_not_ge hn
          have hP : Ordinal.Principal (· + ·) α := Ordinal.principal_add_omega0_opow γ
          have hnlt (n : ℕ) : c.ord * (n : Ordinal) < α := by
            induction n with
            | zero => simpa only [Nat.cast_zero, mul_zero] using Ordinal.omega0_pos.trans_le hα
            | succ n ih =>
                rw [Ordinal.natCast_succ, Ordinal.mul_succ]
                exact hP ih hκlt
          have hb : c.ord * Ordinal.omega0 ≤ α :=
            (Ordinal.mul_le_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mpr (by
              intro b hb
              obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hb
              rw [hn]
              exact (hnlt n).le)
          exact hsmall.not_ge hb
        change HasUPFP 𝕜 (OrdinalContinuous 𝕜 α)
        rw [he]
        exact Posets.initialOrdinal_hasUPFP hreg hu
      · exact Posets.initialOrdinalInfiniteQuotient_hasUPFP hreg hu (le_of_not_gt hsmall) hsq
    · exact Posets.singularInitialBelowSquare_hasUPFP hu.le hreg hlo hsq.le
  · apply ordinal_above_initial_square_hasUPFP c hu α le_rfl
    have he : c.ord ^ (2 : Ordinal.{0}) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    rw [he]
    exact le_of_not_gt hsq

theorem theorem_1_1_smallScalar_smallOrdinal (α : Ordinal.{0}) (p : BanachExponent) :
    Theorem_1_1 𝕜 α p :=
  theorem_1_1_of_canonical_bases omegaPower_base_hasUPFP_small α p

end SmallScalar
attribute [local instance] RingHomInvPair.of_ringEquiv

theorem theorem_1_1_smallOrdinal (𝕜 : Type*) [RCLike 𝕜]
    (α : Ordinal.{0}) (p : BanachExponent) : Theorem_1_1 𝕜 α p := by
  have h : HasUPFP 𝕜 (SequenceSum p (OrdinalContinuous 𝕜 α)) := by
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hr | hc
    · let e := RCLike.realRingEquiv hr
      letI : RingHomIsometric (RingHomClass.toRingHom e) :=
        ⟨fun {x} => (RCLike.realLinearIsometryEquiv hr).norm_map x⟩
      letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
        intro x
        have h := scalarRingEquiv_norm e (e.symm x)
        rw [e.apply_symm_apply] at h
        exact h.symm⟩
      letI : RingHomIsometric (RingHomClass.toRingHom e.symm.symm) := by
        simpa only [RingEquiv.symm_symm] using
          (inferInstance : RingHomIsometric (RingHomClass.toRingHom e))
      exact (theorem_1_1_smallScalar_smallOrdinal (𝕜 := ℝ) α p).1.of_semilinearIsometry
        e.symm (lpSemilinearIsometryEquiv e p.val (ι := ℕ)
          (continuousMapScalarIsometryEquiv e (OrdinalInterval α))).symm
    · let e := RCLike.complexRingEquiv hc
      letI : RingHomIsometric (RingHomClass.toRingHom e) :=
        ⟨fun {x} => (RCLike.complexLinearIsometryEquiv hc).norm_map x⟩
      letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
        intro x
        have h := scalarRingEquiv_norm e (e.symm x)
        rw [e.apply_symm_apply] at h
        exact h.symm⟩
      letI : RingHomIsometric (RingHomClass.toRingHom e.symm.symm) := by
        simpa only [RingEquiv.symm_symm] using
          (inferInstance : RingHomIsometric (RingHomClass.toRingHom e))
      exact (theorem_1_1_smallScalar_smallOrdinal (𝕜 := ℂ) α p).1.of_semilinearIsometry
        e.symm (lpSemilinearIsometryEquiv e p.val (ι := ℕ)
          (continuousMapScalarIsometryEquiv e (OrdinalInterval α))).symm
  exact ⟨h, h.lp_isPrimary⟩

end LPCK
