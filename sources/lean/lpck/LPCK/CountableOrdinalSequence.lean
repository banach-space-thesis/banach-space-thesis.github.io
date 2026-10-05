import LPCK.OrdinalBackground
import LPCK.MainStatements
import ThesisCommon.Analysis.FiniteCompactPrimariness
import ThesisCommon.Analysis.CountableOrdinalSmallModel
import ThesisCommon.Analysis.CountableOrdinalContinuous
import ThesisCommon.Analysis.LpSemilinearIsometry
import ThesisCommon.Analysis.ScalarFactorizationTransport
import ThesisCommon.Analysis.FiniteOrdinalCoefficients

/-! All sequence exponents on actual countable ordinal coefficients. The
canonical ordinal tower supplies base UPFP and a genuine c0 self-isomorphism;
the finite-p and infinity operator reductions are proved separately. -/
noncomputable section
open Set Topology
open scoped ENNReal
namespace LPCK
open ThesisCommon
attribute [local instance] RingHomInvPair.of_ringEquiv
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000
section SmallScalar
variable {𝕜 : Type} [RCLike 𝕜]

def countableCanonicalOrdinalCZeroEquiv (η : Ordinal.{0})
    (hcη : η.card ≤ Cardinal.aleph0) :
    OrdinalContinuous 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ η)) ≃L[𝕜]
      CZeroSum (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ η))) := by
  by_cases hη : η = 0
  · subst η
    rw [Ordinal.opow_zero, Ordinal.opow_one]
    let e := Posets.ordinalOmegaCZeroEquiv (𝕜 := 𝕜)
    exact e.trans (cZeroFlattenEquiv.symm.trans (cZeroMapEquiv (ι := ℕ) e.symm))
  let γ := Ordinal.omega0 ^ η
  let θ := Ordinal.omega0 ^ γ
  have hγinf : Ordinal.omega0 ≤ γ :=
    Posets.countableNormal_power_infinite (Ordinal.one_le_iff_ne_zero.mpr hη)
  have hγ2 : 2 ≤ γ := (Ordinal.nat_lt_omega0 2).le.trans hγinf
  have hcγ : γ.card ≤ Cardinal.aleph0 := by
    dsimp only [γ]
    rw [Ordinal.card_omega0_opow hη]
    exact max_le le_rfl hcη
  have hθinf : Ordinal.omega0 ≤ θ :=
    Posets.countableNormal_power_infinite (Ordinal.one_lt_omega0.le.trans hγinf)
  let e := JLMS.ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) θ hθinf
  exact e.trans ((Posets.countablePowerEndpointReplication (𝕜 := 𝕜) γ hγ2 hcγ).trans
    ((JLMS.CZeroSum.reindex (𝕜 := 𝕜) (E := fun _ : Iio (Ordinal.omega0 : Ordinal.{0}) =>
      JLMS.ordinalEndpointZero 𝕜 θ) Posets.ordinalNatIioOmegaEquiv).toContinuousLinearEquiv.trans
      ((JLMS.CZeroSum.congrRight (fun _ : ℕ => e.symm) (norm_nonneg _) (norm_nonneg _)
        (fun _ => le_rfl) (fun _ => le_rfl)).trans jlmsCZeroMapIsometry.toContinuousLinearEquiv)))

theorem countableCanonicalOrdinal_sequence_hasUPFP (η : Ordinal.{0})
    (hcη : η.card ≤ Cardinal.aleph0) (p : BanachExponent) :
    HasUPFP 𝕜 (SequenceSum p
      (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ η)))) := by
  let γ := Ordinal.omega0 ^ η
  let θ := Ordinal.omega0 ^ γ
  have hX : HasUPFP 𝕜 (OrdinalContinuous 𝕜 θ) :=
    Posets.countableCanonicalOrdinal_hasUPFP η hcη
  have hD : ordinalDerived (Icc 0 θ) γ = {θ} := by
    have heq : Icc (0 : Ordinal.{0}) θ = Iic θ := by ext x; simp
    rw [heq]
    exact ordinalDerived_Iic_power_self (Ordinal.opow_ne_zero η Ordinal.omega0_ne_zero)
  by_cases hpTop : p.val = ∞
  · have hp : p = ⟨∞, by simp⟩ := Subtype.ext hpTop
    subst p
    exact hX.ordinal_infinity hD
  by_cases h1 : p.val = 1
  · have hp : p = ⟨1, le_rfl⟩ := Subtype.ext h1
    subst p
    exact hX.ellOne_of_cZero_equiv (countableCanonicalOrdinalCZeroEquiv η hcη)
  have hreal : 1 < p.val.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by simp) hpTop).mpr
        (lt_of_le_of_ne p.property (Ne.symm h1))
  exact (ordinal_lp_finite_upfp_primary_of_dual_equiv_ellOne hD hpTop hreal hX
    (ordinalContinuousDualEllOneEquiv θ)).1

theorem countableOrdinal_sequence_hasUPFP_smallScalar (α : Ordinal.{0})
    (hcα : α.card ≤ Cardinal.aleph0) (hαinf : Ordinal.omega0 ≤ α)
    (p : BanachExponent) : HasUPFP 𝕜 (SequenceSum p (OrdinalContinuous 𝕜 α)) := by
  obtain ⟨η, hcη, ⟨e⟩⟩ := Posets.exists_countableOrdinal_normal_form
    (𝕜 := 𝕜) α hcα hαinf
  exact (countableCanonicalOrdinal_sequence_hasUPFP η hcη p).of_equiv
    (lpMapEquiv p.val e.symm)

end SmallScalar
universe u

theorem countableOrdinal_sequence_hasUPFP_smallScalar_largeOrdinal
    (𝕜 : Type) [RCLike 𝕜] {α : Ordinal.{u}}
    (hα : α < (Cardinal.aleph 1).ord) (hαinf : Ordinal.omega0 ≤ α) (p : BanachExponent) :
    HasUPFP 𝕜 (SequenceSum p (OrdinalContinuous 𝕜 α)) := by
  obtain ⟨β, hcβ, hβ, ⟨e⟩⟩ := exists_countableOrdinal_small_infinite_model hα hαinf
  exact (countableOrdinal_sequence_hasUPFP_smallScalar (𝕜 := 𝕜) β hcβ hβ p).of_equiv
    (lpMapEquiv p.val (continuousMapHomeomorphEquiv e.symm))

theorem countableOrdinal_sequence_hasUPFP
    (𝕜 : Type*) [RCLike 𝕜] {α : Ordinal.{u}}
    (hα : α < (Cardinal.aleph 1).ord) (hαinf : Ordinal.omega0 ≤ α) (p : BanachExponent) :
    HasUPFP 𝕜 (SequenceSum p (OrdinalContinuous 𝕜 α)) := by
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
    exact (countableOrdinal_sequence_hasUPFP_smallScalar_largeOrdinal ℝ hα hαinf p).of_semilinearIsometry
      e.symm (lpSemilinearIsometryEquiv e p.val (ι := ℕ) (continuousMapScalarIsometryEquiv e (OrdinalInterval α))).symm
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
    exact (countableOrdinal_sequence_hasUPFP_smallScalar_largeOrdinal ℂ hα hαinf p).of_semilinearIsometry
      e.symm (lpSemilinearIsometryEquiv e p.val (ι := ℕ) (continuousMapScalarIsometryEquiv e (OrdinalInterval α))).symm

theorem theorem_1_1_countable {𝕜 : Type*} [RCLike 𝕜] {α : Ordinal.{u}}
    (hα : α < (Cardinal.aleph 1).ord) (p : BanachExponent) : Theorem_1_1 𝕜 α p := by
  by_cases hfinite : α < Ordinal.omega0
  · letI := ordinalInterval_finite hfinite
    exact finiteCompact_lp_upfp_primary (OrdinalInterval α) p.val
  have h := countableOrdinal_sequence_hasUPFP 𝕜 hα (le_of_not_gt hfinite) p
  exact ⟨h, h.lp_isPrimary⟩

theorem ordinal_lt_aleph_one_of_countable_interval (α : Ordinal.{u})
    [Countable (OrdinalInterval α)] : α < (Cardinal.aleph 1).ord := by
  have hc : (Iio α).Countable := (Set.to_countable (Icc (0 : Ordinal.{u}) α)).mono
    (fun (x : Ordinal.{u}) (hx : x ∈ Iio α) =>
      (show x ∈ Icc 0 α from ⟨bot_le, hx.le⟩))
  have hcard := (Cardinal.countable_iff_lt_aleph_one (Iio α)).mp hc.to_subtype
  rw [Ordinal.mk_Iio_ordinal, ← not_le, Cardinal.aleph1_le_lift, not_le] at hcard
  exact Cardinal.lt_ord.mpr hcard

end LPCK

