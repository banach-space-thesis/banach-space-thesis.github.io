import Posets.WolfePreservationBlockJointCapture

/-! One continuous phase test controls the variation defect on every set.
Its error is global and does not increase with the depth of a source tree.
The phase-modified marginal is not asserted to equal the original marginal. -/

noncomputable section
open Set Topology
namespace Posets

section Defect
variable {𝕜 Y : Type*} [RCLike 𝕜] [TopologicalSpace Y]
local instance wolfeBlockPhaseDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 Y →L[𝕜] 𝕜) := inferInstance
local instance wolfeBlockPhaseDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 Y →L[𝕜] 𝕜) := inferInstance

def wolfePhaseDefect (P : JLMS.AtomicDualModel 𝕜 Y)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 Y)) (f : JLMS.CZero 𝕜 Y) (D : Set Y) : ℝ :=
  wolfeMass P μ D - RCLike.re (JLMS.atomicRestriction P D (WeakDual.toStrongDual μ) f)

theorem wolfePhaseDefect_nonneg (P : JLMS.AtomicDualModel 𝕜 Y)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 Y)) (f : JLMS.CZero 𝕜 Y) (hf : ‖f‖ ≤ 1) (D : Set Y) :
    0 ≤ wolfePhaseDefect P μ f D := by
  have h := (RCLike.re_le_norm (JLMS.atomicRestriction P D (WeakDual.toStrongDual μ) f)).trans
    ((JLMS.atomicRestriction P D (WeakDual.toStrongDual μ)).le_opNorm f)
  have hb := mul_le_mul_of_nonneg_left hf
    (norm_nonneg (JLMS.atomicRestriction P D (WeakDual.toStrongDual μ)))
  unfold wolfePhaseDefect wolfeMass
  linarith

theorem wolfePhaseDefect_compl (P : JLMS.AtomicDualModel 𝕜 Y)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 Y)) (f : JLMS.CZero 𝕜 Y) (D : Set Y) :
    wolfePhaseDefect P μ f D + wolfePhaseDefect P μ f Dᶜ =
      ‖WeakDual.toStrongDual μ‖ - RCLike.re (μ f) := by
  have he := congrArg (fun φ : JLMS.CZero 𝕜 Y →L[𝕜] 𝕜 => RCLike.re (φ f))
    (JLMS.atomicRestriction_compl P D (WeakDual.toStrongDual μ))
  simp only [ContinuousLinearMap.sub_apply, map_sub] at he
  have hn := wolfeMass_compl P μ D
  unfold wolfePhaseDefect
  change RCLike.re (μ f) - RCLike.re (JLMS.atomicRestriction P D (WeakDual.toStrongDual μ) f) =
    RCLike.re (JLMS.atomicRestriction P Dᶜ (WeakDual.toStrongDual μ) f) at he
  linarith

theorem wolfePhaseDefect_le_total (P : JLMS.AtomicDualModel 𝕜 Y)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 Y)) (f : JLMS.CZero 𝕜 Y) (hf : ‖f‖ ≤ 1) (D : Set Y) :
    wolfePhaseDefect P μ f D ≤ ‖WeakDual.toStrongDual μ‖ - RCLike.re (μ f) := by
  have he := wolfePhaseDefect_compl P μ f D
  have hn := wolfePhaseDefect_nonneg P μ f hf Dᶜ
  linarith

theorem wolfePhaseRestriction_re_lower (P : JLMS.AtomicDualModel 𝕜 Y)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 Y)) (f : JLMS.CZero 𝕜 Y) (hf : ‖f‖ ≤ 1) (D : Set Y) :
    wolfeMass P μ D - (‖WeakDual.toStrongDual μ‖ - RCLike.re (μ f)) ≤
      RCLike.re (JLMS.atomicRestriction P D (WeakDual.toStrongDual μ) f) := by
  have h := wolfePhaseDefect_le_total P μ f hf D
  unfold wolfePhaseDefect at h
  linarith

end Defect

variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]
local instance wolfeBlockJointPhaseDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 (K × L) →L[𝕜] 𝕜) := inferInstance
local instance wolfeBlockJointPhaseDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 (K × L) →L[𝕜] 𝕜) := inferInstance

theorem wolfeJoint_exists_fixed_phase
    (P : JLMS.AtomicDualModel 𝕜 (K × L)) (hKL : JLMS.IsScattered (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : JLMS.CZero 𝕜 (K × L), ‖f‖ ≤ 1 ∧
      ∃ W : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)), IsOpen W ∧ μ ∈ W ∧
        ∀ ν ∈ W, ∀ η : ℝ, wolfeJointVariation S ν ≤ wolfeJointVariation S μ + η →
          0 ≤ wolfeJointVariation S ν - RCLike.re (wolfeJointLift S ν f) ∧
          wolfeJointVariation S ν - RCLike.re (wolfeJointLift S ν f) < η + ε := by
  obtain ⟨f, hf, _, hnorm⟩ := exists_supported_wolfe_positive_norming P hKL
    (wolfeJointLift S μ) isOpen_univ
    (show wolfeJointVariation S μ - ε < wolfeMass P (wolfeJointLift S μ) univ by
      rw [wolfeMass_univ]
      change wolfeJointVariation S μ - ε < wolfeJointVariation S μ
      linarith)
  let W := {ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K) |
    wolfeJointVariation S μ - ε < RCLike.re (wolfeJointLift S ν f)}
  have hW : IsOpen W := isOpen_lt continuous_const
    (RCLike.continuous_re.comp ((WeakDual.eval_continuous f).comp (wolfeJointLift_continuous S)))
  refine ⟨f, hf, W, hW, hnorm, ?_⟩
  intro ν hν η hn
  have hv : RCLike.re (wolfeJointLift S ν f) ≤ wolfeJointVariation S ν := by
    apply (RCLike.re_le_norm _).trans
    apply ((WeakDual.toStrongDual (wolfeJointLift S ν)).le_opNorm f).trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf
      (norm_nonneg (WeakDual.toStrongDual (wolfeJointLift S ν)))
  change wolfeJointVariation S μ - ε < RCLike.re (wolfeJointLift S ν f) at hν
  exact ⟨by linarith, by linarith⟩

end Posets
