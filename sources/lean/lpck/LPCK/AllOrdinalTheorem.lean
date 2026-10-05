import LPCK.CanonicalOrdinalSequence
import LPCK.GenericOrdinalPrincipal
import LPCK.GenericOrdinalFixedExponent
import LPCK.GenericOrdinalRegularSquare
import LPCK.GenericCZeroInfiniteFactorization
import LPCK.GenericOrdinalSingularBelowSquare
import ThesisCommon.Analysis.CountableOrdinalSmallModel
import Posets.CountableOrdinalUPFPCanonical
import ThesisCommon.Analysis.LpSemilinearIsometry
import ThesisCommon.Analysis.ScalarFactorizationTransport

/-! The original all-ordinal theorem, assembled from actual universe-polymorphic ordinal block arguments. -/
noncomputable section
universe u
namespace LPCK
open ThesisCommon
section SmallScalar
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1800000

theorem initialCanonical_base_hasUPFP_allUniverses (c : Cardinal.{u})
    (hu : Cardinal.aleph0 < c) (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (hgc : g = 2 ∨ (Ordinal.omega0 ≤ g ∧ Ordinal.Principal (· + ·) g)) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ g)) := by
  rcases hgc with rfl | ⟨hgω, hgP⟩
  · have he : c.ord ^ (2 : Ordinal.{u}) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    change HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ (2 : Ordinal.{u})))
    rw [he]
    by_cases hr : c.IsRegular
    · exact GenericOrdinal.regularInitialSquare_hasUPFP hr hu
    · exact GenericOrdinal.singularInitialBelowSquare_hasUPFP hu.le hr
        (Ordinal.le_mul_left _ (Ordinal.omega0_pos.trans_le
          (Cardinal.omega0_le_ord.mpr hu.le))) le_rfl
  · have hP : Ordinal.Principal (· + ·) (c.ord * g) :=
      Ordinal.principal_add_mul_of_principal_add c.ord
        (Ordinal.one_lt_omega0.trans_le hgω).ne' hgP
    have hωκ : Ordinal.omega0 < c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hu
    have hω : Ordinal.omega0 < c.ord * g :=
      hωκ.trans_le (Ordinal.le_mul_left _ (Ordinal.omega0_pos.trans_le hgω))
    exact (GenericOrdinal.principalRank_hasUPFP (𝕜 := 𝕜) (c.ord * g) hP hω).of_equiv
      (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜)
        (Posets.ordinal_uncountable_initial_power_rank hu g)).toContinuousLinearEquiv

theorem ordinal_above_initial_square_hasUPFP_allUniverses (c : Cardinal.{u})
    (hu : Cardinal.aleph0 < c) (α : Ordinal.{u}) (hcard : α.card ≤ c)
    (hα : c.ord ^ (2 : Ordinal.{u}) ≤ α) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) := by
  obtain ⟨g, hg, hgcard, hgc, ⟨e⟩⟩ :=
    GenericOrdinal.exists_ordinalSpace_canonical_power_normalForm (𝕜 := 𝕜) c hu.le α hcard hα
  exact (initialCanonical_base_hasUPFP_allUniverses c hu g hg hgcard hgc).of_equiv e.symm

theorem omegaPower_base_hasUPFP_allUniverses (γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ)) := by
  let α := Ordinal.omega0 ^ γ
  let c := α.card
  have hα : Ordinal.omega0 ≤ α := by
    simpa only [Ordinal.opow_one] using
      (Ordinal.opow_le_opow_right Ordinal.omega0_pos (Ordinal.one_le_iff_ne_zero.mpr hγ))
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
        exact GenericOrdinal.initialOrdinal_hasUPFP hreg hu
      · letI := GenericOrdinal.initialOrdinalInfiniteQuotient_index_infinite hu
          (le_of_not_gt hsmall)
        exact GenericOrdinal.initialOrdinalInfiniteQuotient_hasUPFP_of_scalar
          hreg hu (le_of_not_gt hsmall) hsq
          (GenericOrdinal.jlmsScalarCZero_infinite_hasUPFP _)
    · exact GenericOrdinal.singularInitialBelowSquare_hasUPFP hu.le hreg hlo hsq.le
  · apply ordinal_above_initial_square_hasUPFP_allUniverses c hu α le_rfl
    have he : c.ord ^ (2 : Ordinal.{u}) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    rw [he]
    exact le_of_not_gt hsq

theorem theorem_1_1_smallScalar_allOrdinals (α : Ordinal.{u}) (p : BanachExponent) :
    Theorem_1_1 𝕜 α p :=
  theorem_1_1_of_canonical_bases omegaPower_base_hasUPFP_allUniverses α p

end SmallScalar
attribute [local instance] RingHomInvPair.of_ringEquiv

theorem theorem_1_1_proof (𝕜 : Type*) [RCLike 𝕜]
    (α : Ordinal.{u}) (p : BanachExponent) : Theorem_1_1 𝕜 α p := by
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
      exact (theorem_1_1_smallScalar_allOrdinals (𝕜 := ℝ) α p).1.of_semilinearIsometry
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
      exact (theorem_1_1_smallScalar_allOrdinals (𝕜 := ℂ) α p).1.of_semilinearIsometry
        e.symm (lpSemilinearIsometryEquiv e p.val (ι := ℕ)
          (continuousMapScalarIsometryEquiv e (OrdinalInterval α))).symm
  exact ⟨h, h.lp_isPrimary⟩

end LPCK

