import Posets.WolfePreservationBlockJointLocalization

/-! On a narrow band of total joint variation, every clopen rectangular
variation is approximately continuous with the same error. Complementary
variation gives the upper estimate; no continuity of absolute values of
individual atoms is assumed. -/

noncomputable section
open Set Topology
namespace Posets

theorem wolfeMass_clopen_local_upper {𝕜 Y : Type*} [RCLike 𝕜]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (P : JLMS.AtomicDualModel 𝕜 Y) (hY : JLMS.IsScattered Y)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 Y)) {D : Set Y} (hD : IsClopen D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 Y)), IsOpen W ∧ μ ∈ W ∧
      ∀ ν ∈ W, ∀ η : ℝ, ‖WeakDual.toStrongDual ν‖ ≤ ‖WeakDual.toStrongDual μ‖ + η →
        wolfeMass P ν D < wolfeMass P μ D + η + ε := by
  let W := {ν : WeakDual 𝕜 (JLMS.CZero 𝕜 Y) |
    wolfeMass P μ Dᶜ - ε < wolfeMass P ν Dᶜ}
  refine ⟨W, isOpen_wolfeMass_gt P hY hD.compl.isOpen _, ?_, ?_⟩
  · change wolfeMass P μ Dᶜ - ε < wolfeMass P μ Dᶜ
    linarith
  · intro ν hν η hn
    have hμsum := wolfeMass_compl P μ D
    have hνsum := wolfeMass_compl P ν D
    change wolfeMass P μ Dᶜ - ε < wolfeMass P ν Dᶜ at hν
    linarith

variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

theorem wolfeJointMass_isOpen_gt (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (hKL : JLMS.IsScattered (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    {H : Set K} (hH : IsOpen H) {V : Set L} (hV : IsOpen V) (r : ℝ) :
    IsOpen {μ | r < wolfeJointMass P S μ H V} :=
  (isOpen_wolfeMass_gt P hKL (hH.prod hV) r).preimage (wolfeJointLift_continuous S)

theorem wolfeJointMass_lowerSemicontinuous (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (hKL : JLMS.IsScattered (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    {H : Set K} (hH : IsOpen H) {V : Set L} (hV : IsOpen V) :
    LowerSemicontinuous (fun μ => wolfeJointMass P S μ H V) :=
  lowerSemicontinuous_iff_isOpen_preimage.mpr (wolfeJointMass_isOpen_gt P hKL S hH hV)

theorem wolfeJointMass_local_upper (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (hKL : JLMS.IsScattered (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    {H : Set K} (hH : IsClopen H) {V : Set L} (hV : IsClopen V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)), IsOpen W ∧ μ ∈ W ∧
      ∀ ν ∈ W, ∀ η : ℝ, wolfeJointVariation S ν ≤ wolfeJointVariation S μ + η →
        wolfeJointMass P S ν H V < wolfeJointMass P S μ H V + η + ε := by
  obtain ⟨W, hW, hμ, hbound⟩ := wolfeMass_clopen_local_upper P hKL
    (wolfeJointLift S μ) (hH.prod hV) hε
  exact ⟨wolfeJointLift S ⁻¹' W, hW.preimage (wolfeJointLift_continuous S), hμ,
    fun ν hν η hn => hbound (wolfeJointLift S ν) hν η hn⟩

theorem wolfeJointMass_local_abs_sub (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (hKL : JLMS.IsScattered (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    {H : Set K} (hH : IsClopen H) {V : Set L} (hV : IsClopen V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)), IsOpen W ∧ μ ∈ W ∧
      ∀ ν ∈ W, ∀ η : ℝ, 0 ≤ η →
        wolfeJointVariation S ν ≤ wolfeJointVariation S μ + η →
        |wolfeJointMass P S ν H V - wolfeJointMass P S μ H V| < η + ε := by
  obtain ⟨W, hW, hμW, hup⟩ := wolfeJointMass_local_upper P hKL S μ hH hV hε
  let U := {ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K) |
    wolfeJointMass P S μ H V - ε < wolfeJointMass P S ν H V}
  have hU : IsOpen U := wolfeJointMass_isOpen_gt P hKL S hH.isOpen hV.isOpen _
  refine ⟨W ∩ U, hW.inter hU, ⟨hμW, ?_⟩, ?_⟩
  · change wolfeJointMass P S μ H V - ε < wolfeJointMass P S μ H V
    linarith
  · intro ν hν η hη hn
    have hu := hup ν hν.1 η hn
    have hl : wolfeJointMass P S μ H V - ε < wolfeJointMass P S ν H V := hν.2
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

end Posets
