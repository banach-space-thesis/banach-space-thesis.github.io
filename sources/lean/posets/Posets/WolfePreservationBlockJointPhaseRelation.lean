import Posets.WolfePreservationBlockJointPhaseRows
import Posets.WolfePreservationNecessaryClosedKernelAtoms

/-! The normalized good rows define an actual closed relation on the
original compact target. Its source fibres have a uniform finite bound. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

def wolfeJointPhaseRelation (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ κ d : ℝ) : Set (K × L) :=
  (fun p : wolfeJointPhaseGoodRows N S f τ κ × L => (p.1.val, p.2)) ''
    wolfeClopenKernelRelation (wolfeJointPhaseNormalizedRows N S f τ κ) d

theorem wolfeJointPhaseRelation_mem_iff (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ κ d : ℝ) (y : K) (x : L) :
    (y, x) ∈ wolfeJointPhaseRelation N S f τ κ d ↔
      ∃ hy : y ∈ wolfeJointPhaseGoodRows N S f τ κ,
        (⟨y, hy⟩, x) ∈ wolfeClopenKernelRelation (wolfeJointPhaseNormalizedRows N S f τ κ) d := by
  constructor
  · rintro ⟨⟨⟨z, hz⟩, w⟩, hp, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨hz, hp⟩
  · rintro ⟨hy, hp⟩
    exact ⟨(⟨y, hy⟩, x), hp, rfl⟩

theorem wolfeJointPhaseRelation_isClosed (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ d : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    IsClosed (wolfeJointPhaseRelation N S f τ κ d) := by
  letI : CompactSpace (wolfeJointPhaseGoodRows N S f τ κ) :=
    isCompact_iff_compactSpace.mp (wolfeJointPhaseGoodRows_isClosed N S f τ κ).isCompact
  exact ((wolfeClopenKernelRelation_isClosed _
    (wolfeJointPhaseNormalizedRows_continuous N S f τ hκ) d).isCompact.image
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).isClosed

theorem wolfeJointPhaseRelation_mem_of_coordinate (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ d : ℝ) {κ : ℝ} (hκ : 0 < κ) {y : K} (hy : y ∈ wolfeJointPhaseGoodRows N S f τ κ)
    (x : L) (hatom : (d + τ) * ‖wolfeJointPhaseTotal S f y‖ ≤
      ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y x‖) :
    (y, x) ∈ wolfeJointPhaseRelation N S f τ κ d := by
  apply (wolfeJointPhaseRelation_mem_iff N S f τ κ d y x).mpr
  refine ⟨hy, ?_⟩
  apply wolfeClopenKernelRelation_mem_of_normalized_atom N
    (wolfeJointPhaseNormalizedRows N S f τ κ) ⟨y, hy⟩ x
    (wolfeJointPhaseNormalizedRows_one N S f τ hκ ⟨y, hy⟩)
    (wolfeJointPhaseNormalizedRows_norm_le N S f τ hκ ⟨y, hy⟩)
  change d + τ ≤ ‖N.representation ((wolfeJointPhaseTotal S f y)⁻¹ •
    ((JLMS.evaluation y).comp (wolfeJointPhaseKernel S f))) x‖
  rw [map_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
  change d + τ ≤ (‖wolfeJointPhaseTotal S f y‖)⁻¹ *
    ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y x‖
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ (hκ.trans_le hy.2)).mpr hatom

end Posets

namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [MetricSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [Countable L]

theorem wolfeJointPhaseRelation_uniform_finite_fibres (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ : ℝ) {κ d : ℝ} (hκ : 0 < κ) (hd : 0 < d) :
    ∃ m : ℕ, ∀ y : K, ∀ s : Finset L,
      (∀ x ∈ s, (y, x) ∈ wolfeJointPhaseRelation N S f τ κ d) → s.card ≤ m := by
  obtain ⟨m, hm⟩ := wolfeClopenKernelRelation_uniform_finite_fibres
    (wolfeJointPhaseNormalizedRows N S f τ κ) hd
      (wolfeJointPhaseNormalizedRows_norm_le N S f τ hκ)
  refine ⟨m, ?_⟩
  intro y s hs
  by_cases hy : y ∈ wolfeJointPhaseGoodRows N S f τ κ
  · apply hm ⟨y, hy⟩ s
    intro x hx
    obtain ⟨hy', hr⟩ := (wolfeJointPhaseRelation_mem_iff N S f τ κ d y x).mp (hs x hx)
    exact hr
  · have he : s = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      obtain ⟨hy', _⟩ := (wolfeJointPhaseRelation_mem_iff N S f τ κ d y x).mp (hs x hx)
      exact hy hy'
    simp [he]

end Posets
