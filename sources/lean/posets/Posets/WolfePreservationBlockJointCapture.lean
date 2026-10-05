import Posets.WolfePreservationBlockJointFlat

/-! A compact target window captures the relevant source marginal uniformly
on a neighborhood inside a fixed band of total joint variation. Descendant
source sets are retained by monotonicity of the same rectangular tail. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

theorem wolfeJointMass_compact_target_capture
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (hK : JLMS.IsScattered K) (hKL : JLMS.IsScattered (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    {U : Set K} (hU : IsOpen U) {V : Set L} (hV : IsOpen V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Set K, IsClopen H ∧ IsCompact H ∧ H ⊆ U ∧
      wolfeJointMass P S μ U V - ε < wolfeJointMass P S μ H V := by
  obtain ⟨E, _, hEc, hEU, hEmass⟩ := wolfe_exists_compact_clopen_large_mass
    P hKL (wolfeJointLift S μ) (hU.prod hV)
    (show wolfeJointMass P S μ U V - ε < wolfeMass P (wolfeJointLift S μ) (U ×ˢ V) by
      change wolfeJointMass P S μ U V - ε < wolfeJointMass P S μ U V
      linarith)
  have hproj : Prod.fst '' E ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    exact (hEU hz).1
  obtain ⟨H, hH, hHc, hEH, hHU⟩ := wolfe_exists_compact_clopen_between hK
    (hEc.image continuous_fst) hU hproj
  refine ⟨H, hH, hHc, hHU, hEmass.trans_le (wolfeMass_mono P _ ?_)⟩
  intro z hz
  exact ⟨hEH (mem_image_of_mem Prod.fst hz), (hEU hz).2⟩

theorem wolfeJointMass_kernel_capture_on_band
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L))
    (hK : JLMS.IsScattered K) (hL : JLMS.IsScattered L)
    (hKL : JLMS.IsScattered (K × L))
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {V : Set L} (hV : IsClopen V)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ H : Set K, IsClopen H ∧ IsCompact H ∧ H ⊆ wolfeKernelRegion N S V δ ∧
      ∃ W : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)), IsOpen W ∧ μ ∈ W ∧
        ∀ ν ∈ W, ∀ η : ℝ, wolfeJointVariation S ν ≤ wolfeJointVariation S μ + η →
          ∀ V' : Set L, V' ⊆ V →
            wolfeJointMass P S ν Hᶜ V' < δ * ‖WeakDual.toStrongDual μ‖ + η + 2 * ε := by
  let U := wolfeKernelRegion N S V δ
  have hU : IsOpen U := wolfeKernelRegion_isOpen N hL S hV.isOpen δ
  obtain ⟨H, hH, hHc, hHU, hcapture⟩ :=
    wolfeJointMass_compact_target_capture P hK hKL S μ hU hV.isOpen hε
  have htail : wolfeJointMass P S μ Hᶜ V < δ * ‖WeakDual.toStrongDual μ‖ + ε := by
    have hHsum := wolfeJointMass_target_compl P S μ H V
    have hUsum := wolfeJointMass_target_compl P S μ U V
    have hout := wolfeJointMass_outside_kernel_le M N P S μ V hδ
    change wolfeJointMass P S μ Uᶜ V ≤ δ * ‖WeakDual.toStrongDual μ‖ at hout
    linarith
  obtain ⟨W, hW, hμW, hup⟩ := wolfeJointMass_local_upper P hKL S μ hH.compl hV hε
  refine ⟨H, hH, hHc, hHU, W, hW, hμW, ?_⟩
  intro ν hν η hn V' hVV
  have hbound := hup ν hν η hn
  have hmono : wolfeJointMass P S ν Hᶜ V' ≤ wolfeJointMass P S ν Hᶜ V :=
    wolfeMass_mono P _ (Set.prod_mono subset_rfl hVV)
  linarith

end Posets
