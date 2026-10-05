import Posets.WolfePreservationBlockJointPhaseDiagonal
import Posets.WolfePreservationNecessaryJointBands

/-! Below ω², an identity factorization admits a full requested-rank closed
core and one continuous joint phase with arbitrarily small global defect.
Finite-band pruning absorbs the ordinal cost before the phase is chosen. -/

noncomputable section
open Set Topology ThesisCommon
universe u
namespace Posets
variable {𝕜 K L X : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorizationJoint_fixed_phase_core_below_omega_sq
    (P : JLMS.AtomicDualModel 𝕜 (K × L)) (hKL : JLMS.IsScattered (K × L))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1)
    {A : Set L} (hA : IsClosed A)
    (hrank : (ordinalDerived A ((Ordinal.omega0 : Ordinal.{u}) ^ (2 : Ordinal))).Nonempty)
    {ε : ℝ} (hε : 0 < ε) {β : Ordinal.{u}} (hβ : β < Ordinal.omega0 ^ (2 : Ordinal)) :
    ∃ B : Set L, IsClosed B ∧ B ⊆ A ∧ (ordinalDerived B β).Nonempty ∧
      ∃ f : JLMS.CZero 𝕜 (K × L), ‖f‖ ≤ 1 ∧ ∀ x ∈ B,
        0 ≤ wolfeJointVariation S (wolfeFactorizationLift T R c x) -
          RCLike.re (wolfeJointLift S (wolfeFactorizationLift T R c x) f) ∧
        wolfeJointVariation S (wolfeFactorizationLift T R c x) -
          RCLike.re (wolfeJointLift S (wolfeFactorizationLift T R c x) f) < ε := by
  obtain ⟨a, B, hB, hBA, hx, hband⟩ :=
    wolfeFactorizationJoint_flat_cores_below_omega_sq T R S hfactor c hc hn hA hrank
      (half_pos hε) hβ
  obtain ⟨x, hx⟩ := hx
  have hxB : x ∈ B := by
    simpa using ordinalDerived_antitone hB (show (0 : Ordinal.{u}) ≤ β from bot_le) hx
  obtain ⟨f, hf, W, hW, hμW, hphase⟩ := wolfeJoint_exists_fixed_phase P hKL S
    (wolfeFactorizationLift T R c x) (half_pos hε)
  let U := wolfeFactorizationLift T R c ⁻¹' W
  have hU : IsOpen U := hW.preimage (wolfeFactorizationLift_continuous T R c)
  obtain ⟨C, hC, hCB, hCU, hxC⟩ :=
    wolfe_ordinalDerived_closed_neighborhood_core hB hU β hx hμW
  refine ⟨C, hC, hCB.trans hBA, ⟨x, hxC⟩, f, hf, ?_⟩
  intro y hy
  have hyB := hCB hy
  have hqy : wolfeJointVariation S (wolfeFactorizationLift T R c y) ≤
      wolfeJointVariation S (wolfeFactorizationLift T R c x) + ε / 2 := by
    have h1 := (hband x hxB).1
    have h2 := (hband y hyB).2
    linarith
  have h := hphase (wolfeFactorizationLift T R c y) (hCU hy) (ε / 2) hqy
  exact ⟨h.1, by linarith [h.2]⟩

end Posets
