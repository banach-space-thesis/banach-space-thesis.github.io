import BanachIsometric.SphereSignedDegree
import BanachIsometric.SignedCountExcision

/-!
# Nonzero actual sphere degree forces surjectivity

The compact cone image contains the open unit ball because its actual count
is nonzero almost everywhere there. A half-unit target vector in that image
then gives an actual preimage under the sphere map.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal

theorem subset_image_of_ae_signedFiberCount_eq_nonzero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (μ : Measure E) [Measure.IsOpenPosMeasure μ]
    {f : E → E} {D : E → E →L[ℝ] E} {s U : Set E}
    (hs : IsCompact s) (hf : ContinuousOn f s) (hU : IsOpen U) {d : ℤ} (hd : d ≠ 0)
    (hcount : ∀ᵐ y ∂μ, y ∈ U → signedFiberCount f D s y = d) : U ⊆ f '' s := by
  intro y hy
  by_contra hnot
  let W : Set E := U ∩ (f '' s)ᶜ
  have hW : IsOpen W := hU.inter (hs.image_of_continuousOn hf).isClosed.isOpen_compl
  have hnon : μ W ≠ 0 := hW.measure_ne_zero μ ⟨y, hy, hnot⟩
  have hfalse : ∀ᵐ z ∂μ, z ∈ W → False := by
    filter_upwards [hcount] with z hz
    intro hzW
    have hzero := signedFiberCount_eq_zero_of_not_mem_image f D s z hzW.2
    exact hd ((hz hzW.1).symm.trans hzero)
  obtain ⟨z, hz, h⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hnon (ae_restrict_of_ae hfalse)
  exact h hz

theorem sphereSignedDegree_surjective_of_ne_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    (hdegree : sphereSignedDegree e φ ≠ 0) : Function.Surjective φ := by
  let μ : Measure V := Measure.map e.symm volume
  letI : μ.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map volume
  obtain ⟨L, hL⟩ := exists_lipschitz_unitSphereCone hφ
  have hcover : ball (0 : V) 1 ⊆ unitSphereCone φ '' closedBall (0 : V) 1 :=
    subset_image_of_ae_signedFiberCount_eq_nonzero μ (isCompact_closedBall _ _)
      hL.continuous.continuousOn isOpen_ball hdegree
      (ae_unitSphereCone_count_eq_sphereSignedDegree μ e hφ)
  intro u
  have hu : ‖(u : V)‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using u.property
  have hv : (1 / 2 : ℝ) • (u : V) ∈ ball (0 : V) 1 := by
    rw [mem_ball, dist_zero_right, norm_smul, hu]
    norm_num
  obtain ⟨x, _hxball, hfx⟩ := hcover hv
  have hnorm : ‖x‖ = (1 / 2 : ℝ) := by
    rw [← norm_unitSphereCone φ x, hfx, norm_smul, hu]
    norm_num
  have hx : x ≠ 0 := by intro hz; rw [hz, norm_zero] at hnorm; norm_num at hnorm
  refine ⟨coneDirection x hx, ?_⟩
  apply Subtype.ext
  rw [unitSphereCone, coneExtension_of_ne _ x hx, hnorm] at hfx
  have hh := congrArg (fun v : V => (2 : ℝ) • v) hfx
  simpa only [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] using hh

end BanachIsometric
