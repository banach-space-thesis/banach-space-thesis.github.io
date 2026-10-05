import Posets.WolfePreservationMultiplierTransportCore
import Posets.WolfePreservationBlockJointPhaseKernel

/-! Concrete adjoints of multiplication satisfy the setwise bound required
by the compact Wolfe transport. Closed cores in compact metric parameter
spaces supply the sequential compactness used by its induction. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

local instance wolfeMultiplierTransportDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeMultiplierTransportDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfeMass_multiplier_le (M : JLMS.AtomicDualModel 𝕜 K)
    (h : JLMS.CZero 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : Set K) :
    wolfeMass M (weakStarAdjoint (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 K) h) μ) U ≤
      ‖h‖ * wolfeMass M μ U := by
  classical
  let σ := weakStarAdjoint (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 K) h) μ
  have hm (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
      HasSum (U.indicator (fun x => ‖M.representation (WeakDual.toStrongDual ν) x‖))
        (wolfeMass M ν U) := by
    rw [wolfeMass_eq_tsum]
    exact ((JLMS.ellOneOn_summable_norm _).indicator U).hasSum
  apply hasSum_le _ (hm σ) ((hm μ).mul_left ‖h‖)
  intro x
  by_cases hx : x ∈ U
  · simp only [indicator_of_mem hx]
    change ‖M.representation ((WeakDual.toStrongDual μ).comp
      (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 K) h)) x‖ ≤
        ‖h‖ * ‖M.representation (WeakDual.toStrongDual μ) x‖
    rw [wolfeAtomicCoordinate_multiply, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (h.toBCF.norm_coe_le_norm x) (norm_nonneg _)
  · simp [hx]

theorem wolfe_closed_mass_transport
    {P : Type*} [MetricSpace P] [CompactSpace P]
    (M : JLMS.AtomicDualModel 𝕜 K)
    (μ σ : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (hμ : Continuous μ) (hσ : Continuous σ)
    {A : Set P} (hA : IsClosed A) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ p ∈ A, ∀ U, wolfeMass M (σ p) U ≤ C * wolfeMass M (μ p) U)
    (ε : ℝ) (α : Ordinal.{u}) :
    ∀ z ∈ wolfeFamily M ε (σ '' A) α,
      ∃ p ∈ A, σ p = z.1 ∧ (μ p, z.2) ∈ wolfeFamily M (ε / C) (μ '' A) α := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  intro z hz
  have hrσ : range (σ ∘ (Subtype.val : A → P)) = σ '' A := by
    ext x
    simp
  have hrμ : range (μ ∘ (Subtype.val : A → P)) = μ '' A := by
    ext x
    simp
  rw [← hrσ] at hz
  obtain ⟨p, hp, hw⟩ := wolfe_compact_mass_transport M
    (μ ∘ (Subtype.val : A → P)) (σ ∘ (Subtype.val : A → P))
    (hμ.comp continuous_subtype_val) (hσ.comp continuous_subtype_val) hC
    (fun p U => hbound p.val p.property U) ε α z hz
  rw [hrμ] at hw
  exact ⟨p.val, p.property, hp, hw⟩

theorem wolfe_closed_multiplier_transport
    {P : Type*} [MetricSpace P] [CompactSpace P]
    (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    (h : JLMS.CZero 𝕜 K) {C : ℝ} (hC : 0 < C) (hh : ‖h‖ ≤ C)
    {A : Set P} (hA : IsClosed A) (ε : ℝ) (α : Ordinal.{u}) :
    ∀ z ∈ wolfeFamily M ε
      ((fun p => weakStarAdjoint (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 K) h) (μ p)) '' A) α,
      ∃ p ∈ A,
        weakStarAdjoint (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 K) h) (μ p) = z.1 ∧
        (μ p, z.2) ∈ wolfeFamily M (ε / C) (μ '' A) α := by
  apply wolfe_closed_mass_transport M μ _ hμ
    ((weakStarAdjoint_continuous _).comp hμ) hA hC _ ε α
  intro p _ U
  exact (wolfeMass_multiplier_le M h (μ p) U).trans
    (mul_le_mul_of_nonneg_right hh (wolfeMass_nonneg M (μ p) U))

theorem wolfe_closed_multiplier_transport_nonempty
    {P : Type*} [MetricSpace P] [CompactSpace P]
    (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    (h : JLMS.CZero 𝕜 K) {C : ℝ} (hC : 0 < C) (hh : ‖h‖ ≤ C)
    {A : Set P} (hA : IsClosed A) (ε : ℝ) (α : Ordinal.{u})
    (hne : (wolfeFamily M ε
      ((fun p => weakStarAdjoint (ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 K) h) (μ p)) '' A) α).Nonempty) :
    (wolfeFamily M (ε / C) (μ '' A) α).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨p, _, _, hp⟩ := wolfe_closed_multiplier_transport M μ hμ h hC hh hA ε α z hz
  exact ⟨(μ p, z.2), hp⟩

end Posets
