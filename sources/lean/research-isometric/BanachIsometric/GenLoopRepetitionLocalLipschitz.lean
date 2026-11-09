import BanachIsometric.CubeHalfLipschitz
import BanachIsometric.SphereRepetitionFiberCoordinates

/-! The literal repetition is locally Lipschitz near every non-basepoint
fiber whenever the original cubical loop has that property. The proof uses
the actual affine branches and excludes their dividing hyperplanes from the
actual fiber; no global Lipschitz property of the quotient generator is used. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology Topology.Homotopy NNReal unitInterval

theorem exists_lipschitzOn_repeatGenLoop_nhds_of_nonbase
    {N X : Type*} [DecidableEq N] [Fintype N] [PseudoMetricSpace X] {x z : X}
    (i : N) (p : GenLoop N X x) (hz : z ≠ x)
    (hp : ∀ u : N → unitInterval, p u = z →
      ∃ L : ℝ≥0, ∃ U ∈ 𝓝 u, LipschitzOnWith L p U)
    (d : ℕ) (u : N → unitInterval) (hu : repeatGenLoop i p d u = z) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 u, LipschitzOnWith L (repeatGenLoop i p d) U := by
  induction d generalizing u with
  | zero => exact (hz hu.symm).elim
  | succ d ih =>
    have hmid := repeatGenLoop_fiber_coordinate_ne_half i p hz (d + 1) ⟨u, hu⟩
    have hcoord : Continuous (fun w : N → unitInterval => (w i : ℝ)) :=
      continuous_subtype_val.comp (continuous_apply i)
    by_cases hleft : (u i : ℝ) < 1 / 2
    · have hv : repeatGenLoop i p d (leftExpandCube i u) = z := by
        simpa only [repeatGenLoop_succ, GenLoop.transAt, GenLoop.coe_copy, if_pos hleft.le] using hu
      obtain ⟨L, U, hU, hLip⟩ := ih _ hv
      let W := (leftExpandCube i ⁻¹' U) ∩ {w | (w i : ℝ) < 1 / 2}
      have hW : W ∈ 𝓝 u := Filter.inter_mem
        ((lipschitz_leftExpandCube i).continuous.continuousAt.preimage_mem_nhds hU)
        ((isOpen_lt hcoord continuous_const).mem_nhds hleft)
      have hcomp : LipschitzOnWith (L * 2) (fun w => repeatGenLoop i p d (leftExpandCube i w)) W :=
        hLip.comp (lipschitz_leftExpandCube i).lipschitzOnWith (fun _ hw => hw.1)
      refine ⟨L * 2, W, hW, LipschitzOnWith.of_dist_le_mul ?_⟩
      intro a ha b hb
      have he (w : N → unitInterval) (hw : w ∈ W) :
          repeatGenLoop i p (d + 1) w = repeatGenLoop i p d (leftExpandCube i w) := by
        have hw' : (w i : ℝ) < 1 / 2 := hw.2
        simp only [repeatGenLoop_succ, GenLoop.transAt, GenLoop.coe_copy, if_pos hw'.le]
        rfl
      rw [he a ha, he b hb]
      exact hcomp.dist_le_mul a ha b hb
    · have hright : 1 / 2 < (u i : ℝ) := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hmid)
      have hv : p (rightExpandCube i u) = z := by
        simpa only [repeatGenLoop_succ, GenLoop.transAt, GenLoop.coe_copy,
          if_neg (not_le.mpr hright)] using hu
      obtain ⟨L, U, hU, hLip⟩ := hp _ hv
      let W := (rightExpandCube i ⁻¹' U) ∩ {w | 1 / 2 < (w i : ℝ)}
      have hW : W ∈ 𝓝 u := Filter.inter_mem
        ((lipschitz_rightExpandCube i).continuous.continuousAt.preimage_mem_nhds hU)
        ((isOpen_lt continuous_const hcoord).mem_nhds hright)
      have hcomp : LipschitzOnWith (L * 2) (fun w => p (rightExpandCube i w)) W :=
        hLip.comp (lipschitz_rightExpandCube i).lipschitzOnWith (fun _ hw => hw.1)
      refine ⟨L * 2, W, hW, LipschitzOnWith.of_dist_le_mul ?_⟩
      intro a ha b hb
      have he (w : N → unitInterval) (hw : w ∈ W) :
          repeatGenLoop i p (d + 1) w = p (rightExpandCube i w) := by
        have hw' : 1 / 2 < (w i : ℝ) := hw.2
        simp only [repeatGenLoop_succ, GenLoop.transAt, GenLoop.coe_copy,
          if_neg (not_le.mpr hw')]
        rfl
      rw [he a ha, he b hb]
      exact hcomp.dist_le_mul a ha b hb

end BanachIsometric
