import Posets.WolfePreservationNecessaryMass

/-! The genuine cross-space atomic identity behind Wolfe necessity. For an
identity factorization R T S = I, the lifted measures and the rows of S satisfy
the scalar identity Σ μₓ(y)(S*δᵧ)(x) = c. Its large-coordinate mass and finite
overlap consequences are uniform in x. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]

local instance wolfeNecessaryAtomicDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance
local instance wolfeNecessaryAtomicDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance

def wolfeAtomicCoordinate (N : JLMS.AtomicDualModel 𝕜 L) (x : L) :
    (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  ({ toFun := fun φ => N.representation φ x
     map_add' := by intro φ ψ; simp
     map_smul' := by intro c φ; simp } :
       (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜).mkContinuous 1 (fun φ => by
    simpa only [one_mul, N.representation.norm_map] using
      lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0) (N.representation φ) x)

def wolfeAtomicCrossRow (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (y : K) : JLMS.ellOneOn 𝕜 L :=
  N.representation ((JLMS.evaluation y).comp S)

theorem wolfeAtomicCrossRow_norm_le (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (y : K) :
    ‖wolfeAtomicCrossRow N S y‖ ≤ ‖S‖ := by
  rw [wolfeAtomicCrossRow, N.representation.norm_map]
  exact (ContinuousLinearMap.opNorm_comp_le _ S).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (JLMS.norm_evaluation_le (𝕜 := 𝕜) y) (norm_nonneg S))

theorem wolfeAtomicCrossRow_apply_le (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (y : K) (x : L) :
    ‖wolfeAtomicCrossRow N S y x‖ ≤ ‖S‖ :=
  (lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0) _ x).trans
    (wolfeAtomicCrossRow_norm_le N S y)

theorem wolfeAtomicCrossRow_pairing (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (μ : JLMS.CZero 𝕜 K →L[𝕜] 𝕜) (x : L) :
    HasSum (fun y => M.representation μ y * wolfeAtomicCrossRow N S y x)
      (N.representation (μ.comp S) x) := by
  let A := (wolfeAtomicCoordinate N x).comp (JLMS.banachAdjoint S)
  have h := (JLMS.atomicDual_hasSum M μ).map A A.continuous
  convert h using 1
  funext y
  rw [Function.comp_apply, map_smul]
  rfl

theorem wolfeAtomicCrossRow_finset_overlap (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (y : K) {δ : ℝ} (s : Finset L)
    (hs : ∀ x ∈ s, δ ≤ ‖wolfeAtomicCrossRow N S y x‖) :
    (s.card : ℝ) * δ ≤ ‖S‖ :=
  (wolfe_large_coordinates_finset_bound _ s hs).trans (wolfeAtomicCrossRow_norm_le N S y)

section Factorization
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorizationLift_atomic_identity (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L)
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (x : L) :
    HasSum (fun y => M.representation (WeakDual.toStrongDual
      (wolfeFactorizationLift T R c x)) y * wolfeAtomicCrossRow N S y x) c := by
  classical
  have hp : N.representation (JLMS.evaluation x) = lp.single 1 x (1 : 𝕜) := by
    rw [← N.pointMass x, N.representation.apply_symm_apply]
  have he : (WeakDual.toStrongDual (wolfeFactorizationLift T R c x)).comp S =
      c • JLMS.evaluation x := by
    exact congrArg WeakDual.toStrongDual (wolfeFactorizationLift_pullback T R S hfactor c x)
  have h := wolfeAtomicCrossRow_pairing M N S
    (WeakDual.toStrongDual (wolfeFactorizationLift T R c x)) x
  rw [he, map_smul, hp] at h
  simpa using h

theorem wolfeFactorizationLift_large_coordinate_mass (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L)
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1) (x : L) :
    ‖c‖ / (2 * (‖S‖ + 1)) ≤ wolfeMass M (wolfeFactorizationLift T R c x)
      {y | ‖c‖ / (2 * (‖T‖ + 1)) ≤ ‖wolfeAtomicCrossRow N S y x‖} := by
  rw [wolfeMass, JLMS.atomicRestriction_norm]
  apply wolfe_large_coordinates_mass_lower _ _ (by positivity) (norm_pos_iff.mpr hc)
    (by simpa only [M.representation.norm_map] using wolfeFactorizationLift_norm_le T R c hn x)
    (fun y => (wolfeAtomicCrossRow_apply_le N S y x).trans (by linarith))
    (wolfeFactorizationLift_atomic_identity M N T R S hfactor c x) le_rfl

end Factorization
end Posets
