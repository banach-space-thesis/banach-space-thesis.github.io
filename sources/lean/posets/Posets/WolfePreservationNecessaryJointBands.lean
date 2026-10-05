import Posets.WolfePreservationNecessaryBands
import Posets.WolfePreservationBlockJointVariation
import Mathlib.SetTheory.Ordinal.Principal

/-! The generic finite-band rank estimate applied to the actual joint
functional supplied by an identity factorisation. Its number of bands is
chosen before the requested ordinal rank. -/

noncomputable section
open Set Filter Topology ThesisCommon
universe u
namespace Posets
variable {𝕜 K L X : Type*} [RCLike 𝕜]
    [TopologicalSpace K] [TopologicalSpace L]
    [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]

local instance wolfeNecessaryJointBandsDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 (K × L) →L[𝕜] 𝕜) := inferInstance
local instance wolfeNecessaryJointBandsDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 (K × L) →L[𝕜] 𝕜) := inferInstance

theorem wolfeFactorizationJoint_norm_ge
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (x : L) :
    ‖c‖ ≤ wolfeJointVariation S (wolfeFactorizationLift T R c x) := by
  let f := wolfeSourceBlock (𝕜 := 𝕜) (Set.univ : Set L) isClopen_univ
  let μ := wolfeJointLift S (wolfeFactorizationLift T R c x)
  have hv : μ (wolfeJointSecondPullback f) = c := by
    have h := congrArg (fun φ : WeakDual 𝕜 (JLMS.CZero 𝕜 L) => φ f)
      (wolfeFactorizationJoint_second T R S hfactor c x)
    change μ (wolfeJointSecondPullback f) = c * f x at h
    simpa [f] using h
  have hf : ‖wolfeJointSecondPullback (K := K) f‖ ≤ 1 := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    exact (mul_le_mul wolfeJointSecondPullback_norm_le
      (wolfeSourceBlock_norm_le (𝕜 := 𝕜) univ isClopen_univ)
      (norm_nonneg _) (by norm_num)).trans (by norm_num)
  calc
    ‖c‖ = ‖μ (wolfeJointSecondPullback f)‖ := congrArg norm hv.symm
    _ ≤ ‖WeakDual.toStrongDual μ‖ * ‖wolfeJointSecondPullback f‖ :=
      (WeakDual.toStrongDual μ).le_opNorm _
    _ ≤ ‖WeakDual.toStrongDual μ‖ := by
      simpa using mul_le_mul_of_nonneg_left hf (norm_nonneg (WeakDual.toStrongDual μ))
    _ = _ := rfl

theorem wolfeFactorizationJoint_exists_uniform_band_cores
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1)
    {A : Set L} (hA : IsClosed A) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ ∀ β : Ordinal.{u},
      (ordinalDerived A (β * (N : Ordinal))).Nonempty →
      ∃ j < N, ∃ B : Set L, IsClosed B ∧ B ⊆ A ∧
        (ordinalDerived B β).Nonempty ∧ ∀ x ∈ B,
        (j : ℝ) * η < wolfeJointVariation S (wolfeFactorizationLift T R c x) ∧
        wolfeJointVariation S (wolfeFactorizationLift T R c x) ≤ (j + 1 : ℕ) * η := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖T‖ * ‖S‖) / η)
  have hNpos : 0 < N := by
    have hnonneg : 0 ≤ (‖T‖ * ‖S‖) / η := by positivity
    exact_mod_cast hnonneg.trans_lt hN
  refine ⟨N, hNpos, ?_⟩
  intro β hβ
  apply wolfe_lowerSemicontinuous_band_core hA
    (fun x => wolfeJointVariation S (wolfeFactorizationLift T R c x))
    ((wolfeJointVariation_lowerSemicontinuous S).comp_continuous
      (wolfeFactorizationLift_continuous T R c)) hη N
    (fun x _ => (norm_pos_iff.mpr hc).trans_le (wolfeFactorizationJoint_norm_ge T R S hfactor c x))
    (fun x _ => (wolfeFactorizationJoint_norm_le T R S c hn x).trans
      ((div_lt_iff₀ hη).mp hN).le) β hβ

theorem wolfeFactorizationJoint_flat_cores_below_omega_sq
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1)
    {A : Set L} (hA : IsClosed A)
    (hrank : (ordinalDerived A ((Ordinal.omega0 : Ordinal.{u}) ^ (2 : Ordinal))).Nonempty)
    {η : ℝ} (hη : 0 < η) {β : Ordinal.{u}}
    (hβ : β < Ordinal.omega0 ^ (2 : Ordinal)) :
    ∃ a : ℝ, ∃ B : Set L, IsClosed B ∧ B ⊆ A ∧
      (ordinalDerived B β).Nonempty ∧ ∀ x ∈ B,
      a < wolfeJointVariation S (wolfeFactorizationLift T R c x) ∧
      wolfeJointVariation S (wolfeFactorizationLift T R c x) ≤ a + η := by
  obtain ⟨N, _, hcores⟩ :=
    wolfeFactorizationJoint_exists_uniform_band_cores T R S hfactor c hc hn hA hη
  have hβN : β * (N : Ordinal) < Ordinal.omega0 ^ (2 : Ordinal.{u}) :=
    Ordinal.mul_lt_omega0_opow (by norm_num) hβ (Ordinal.nat_lt_omega0 N)
  obtain ⟨j, _, B, hB, hBA, hBβ, hq⟩ :=
    hcores β (hrank.mono (ordinalDerived_antitone hA hβN.le))
  refine ⟨j * η, B, hB, hBA, hBβ, ?_⟩
  intro x hx
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hq x hx

end Posets
