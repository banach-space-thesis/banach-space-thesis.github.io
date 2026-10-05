import ThesisCommon.Analysis.OrdinalBackwardReduction
import ThesisCommon.Analysis.CotypeUpperSelection

/-! Finite input blocks on actual characteristic-one compact ordinal
intervals. The finite closed-cover theorem supplies a closed self-copy. -/
noncomputable section
open scoped ENNReal BigOperators
universe u
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem ordinal_characteristic_one_exists_small_block {α η a : Ordinal.{u}}
    (hD : ordinalDerived (Set.Icc 0 α) η = {a})
    {N : ℕ} (J : Fin N → X →L[𝕜] Y)
    (hJ : ∀ x : Fin N → X, (∀ i, ‖x i‖ ≤ 1) → ‖∑ i, J i (x i)‖ ≤ 1)
    (T : Y →L[𝕜] OrdinalContinuous 𝕜 α) {M ε : ℝ} (hε : 0 ≤ ε)
    (hT : ‖T‖ ≤ M) (hlarge : M < (N : ℝ) * ε) :
    ∃ (i : Fin N) (c : OrdinalClosedCopy α α),
      ‖((ordinalCopyRead c).comp T).comp (J i)‖ ≤ ε := by
  let B : Fin N → Set (OrdinalInterval α) := fun i => continuousMapSmallSet (T.comp (J i)) ε
  have hcover : ⋃ i, B i = Set.univ := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact continuousMap_small_sets_cover J hJ T
      (by simpa only [mul_one] using hT.trans_lt hlarge) t
  obtain ⟨i, c, hc⟩ := ordinal_characteristic_one_subspace_cover hD B
    (fun i => isClosed_continuousMapSmallSet _ _) hcover
  refine ⟨i, c, ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε
  intro x hx
  apply (ContinuousMap.norm_le _ hε).2
  intro t
  exact hc t x hx.le

end ThesisCommon
