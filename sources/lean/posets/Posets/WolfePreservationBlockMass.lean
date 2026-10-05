import Posets.WolfePreservationBlockFunctions

/-! An identity factorization supplies uniformly large mass on the open
threshold region of each continuous block image, for every parameter in
the entire source clopen block. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L X : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace L] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorizationLift_block_open_mass
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1)
    (V : Set L) (hV : IsClopen V) (x : L) (hx : x ∈ V) :
    ‖c‖ / (2 * (‖S‖ + 1)) ≤ wolfeMass M (wolfeFactorizationLift T R c x)
      (wolfeBlockOpen S V hV ((‖c‖ / (2 * (‖T‖ + 1))) / 2)) := by
  let μ := wolfeFactorizationLift T R c x
  let f := wolfeBlockImage S V hV
  have hpair : HasSum (fun y => M.representation (WeakDual.toStrongDual μ) y * f y) c := by
    have h := JLMS.atomicDual_apply_hasSum M (WeakDual.toStrongDual μ) f
    have he : WeakDual.toStrongDual μ f = c := by
      change wolfeFactorizationLift T R c x (wolfeBlockImage S V hV) = c
      rw [wolfeFactorizationLift_block_pairing T R S hfactor c V hV x, if_pos hx]
    rw [he] at h
    exact h
  have hmass := wolfe_large_coordinates_mass_lower
    (M.representation (WeakDual.toStrongDual μ)) (fun y => f y)
    (show 0 < ‖S‖ + 1 by positivity) (norm_pos_iff.mpr hc)
    (show ‖M.representation (WeakDual.toStrongDual μ)‖ ≤ ‖T‖ by
      simpa only [M.representation.norm_map] using wolfeFactorizationLift_norm_le T R c hn x)
    (fun y => (wolfeBlockImage_apply_le S V hV y).trans (by linarith)) hpair le_rfl
  have hh : ‖c‖ / (2 * (‖S‖ + 1)) ≤ wolfeMass M μ
      {y | ‖c‖ / (2 * (‖T‖ + 1)) ≤ ‖f y‖} := by
    simpa only [wolfeMass, JLMS.atomicRestriction_norm] using hmass
  apply hh.trans (wolfeMass_mono M μ ?_)
  intro y hy
  exact (half_lt_self (div_pos (norm_pos_iff.mpr hc) (by positivity))).trans_le hy

end Posets
