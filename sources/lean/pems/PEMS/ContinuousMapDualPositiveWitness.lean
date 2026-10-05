import PEMS.ALDisjointPositiveWitness
import ThesisCommon.Analysis.ContinuousMapDualAL
import ThesisCommon.Analysis.ContinuousMapComplexDualAL

/-! Disjoint positive real-dual fragments for actual operators between
C(K) duals. The complex fragments are returned in the real continuous dual,
where their positive regular Riesz measures can be used directly. -/
noncomputable section
set_option maxSynthPendingDepth 3
open ThesisCommon Filter Topology
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice
namespace PEMS
variable {K L : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L] [T2Space L]

theorem exists_real_continuousMapDual_disjoint_positiveWitness
    (T : StrongDual ℝ C(K, ℝ) →L[ℝ] StrongDual ℝ C(L, ℝ))
    (hT : ¬IsWeaklyCompactOperator T) :
    ∃ (x : ℕ → StrongDual ℝ C(K, ℝ)) (ψ : ℕ → StrongDual ℝ C(L, ℝ)) (l : ℝ),
      (∀ n, ‖x n‖ = 1) ∧ (∀ n, 0 ≤ ψ n) ∧ (∀ n, ψ n ≤ |T (x n)|) ∧
      (Pairwise fun i j => ψ i ⊓ ψ j = 0) ∧ weakEssentialNorm T ≤ l ∧
      Tendsto (fun n => ‖ψ n‖) atTop (𝓝 l) :=
  exists_real_AL_disjoint_positiveWitness T continuousMap_real_dual_isALSpace
    continuousMapDual_norm_add_of_nonneg hT

theorem exists_complex_continuousMapDual_disjoint_positiveWitness
    (T : StrongDual ℂ C(K, ℂ) →L[ℂ] StrongDual ℂ C(L, ℂ))
    (hT : ¬IsWeaklyCompactOperator T) :
    ∃ (x : ℕ → StrongDual ℂ C(K, ℂ)) (ψ : ℕ → StrongDual ℝ C(L, ℝ)) (l : ℝ),
      (∀ n, ‖x n‖ = 1) ∧ (∀ n, 0 ≤ ψ n) ∧
      (∀ n, ψ n ≤ continuousMapComplexModulus (T (x n))) ∧
      (Pairwise fun i j => ψ i ⊓ ψ j = 0) ∧ weakEssentialNorm T ≤ l ∧
      Tendsto (fun n => ‖ψ n‖) atTop (𝓝 l) := by
  let B := continuousMapComplexDualBanachLatticeModel (K := L)
  let e : B.realForm ≃ₗᵢ[ℝ] StrongDual ℝ C(L, ℝ) := continuousMapDualRealFormEquiv
  have hB : ∀ φ ψ : B.realForm, 0 ≤ φ → 0 ≤ ψ → ‖φ+ψ‖ = ‖φ‖+‖ψ‖ := by
    intro φ ψ hφ hψ
    rw [← e.norm_map (φ+ψ), ← e.norm_map φ, ← e.norm_map ψ, map_add]
    exact continuousMapDual_norm_add_of_nonneg _ _ hφ hψ
  obtain ⟨x, ψ, l, hx, hψ, hle, hd, hl, ht⟩ :=
    exists_complex_AL_disjoint_positiveWitness T continuousMap_complex_dual_isALSpace B hB hT
  refine ⟨x, fun n => e (ψ n), l, hx, hψ, ?_, ?_, hl, ?_⟩
  · intro n
    have h := hle n
    change e (ψ n) ≤ e (e.symm (continuousMapComplexModulus (T (x n)))) at h
    simpa only [e.apply_symm_apply] using h
  · intro i j hij
    have h := congrArg e (hd hij)
    change e (e.symm (e (ψ i) ⊓ e (ψ j))) = e 0 at h
    simpa only [e.apply_symm_apply, map_zero] using h
  · simpa only [e.norm_map] using ht

end PEMS
