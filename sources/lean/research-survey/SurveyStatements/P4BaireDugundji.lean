import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import SurveyStatements.P4BaireMetricParacompact
import Mathlib.Tactic.Linarith

/-! The continuous extension needed for the inverse isometry from the closed
adjoint image in C(W). It is constructed using genuine local convex selection. -/

noncomputable section
set_option autoImplicit false

open Set Filter Topology Metric

namespace SurveyStatements.P4

variable {H E : Type*} [MetricSpace H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An isometry from a closed subset of a metric space into a normed real
space extends continuously to the whole metric space. -/
theorem exists_continuous_extension_of_isometry_closed
    (A : Set H) (hA : IsClosed A) (f : A → E) (hf : Isometry f) :
    ∃ g : C(H, E), ∀ a : A, g a.val = f a := by
  classical
  by_cases hne : A.Nonempty
  · let U := Aᶜ
    let t : U → Set E := fun x => ⋂ a : A, closedBall (f a) (3 * dist x.val a.val)
    have ht : ∀ x, Convex ℝ (t x) := fun x =>
      convex_iInter (fun a => convex_closedBall (f a) _)
    have hlocal : ∀ x : U, ∃ c : E, ∀ᶠ y in 𝓝 x, c ∈ t y := by
      intro x
      let δ := infDist x.val A
      have hδ : 0 < δ := (hA.notMem_iff_infDist_pos hne).mp x.property
      obtain ⟨z, hz, hnear⟩ := (infDist_lt_iff hne).mp
        (show infDist x.val A < (3 / 2 : ℝ) * δ by dsimp [δ]; linarith)
      let a₀ : A := ⟨z, hz⟩
      refine ⟨f a₀, ?_⟩
      filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < δ / 8)] with y hy
      apply Set.mem_iInter.mpr
      intro a
      rw [mem_closedBall, hf.dist_eq, Subtype.dist_eq]
      have hxy : dist x.val y.val < δ / 8 := by
        simpa only [mem_ball, Subtype.dist_eq, dist_comm] using hy
      have hδa : δ ≤ dist x.val a.val := infDist_le_dist_of_mem a.property
      have hza : dist z a.val ≤ dist z x.val + dist x.val a.val := dist_triangle _ _ _
      have hxya : dist x.val a.val ≤ dist x.val y.val + dist y.val a.val :=
        dist_triangle _ _ _
      have hnear' : dist z x.val < (3 / 2 : ℝ) * δ := by
        simpa only [dist_comm] using hnear
      change dist z a.val ≤ 3 * dist y.val a.val
      nlinarith
    obtain ⟨q, hq⟩ := exists_continuous_forall_mem_convex_of_local_const ht hlocal
    let G : H → E := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else q ⟨x, hx⟩
    have hGoff : ContinuousOn G Aᶜ := by
      apply continuousOn_iff_continuous_restrict.mpr
      have heq : (fun x : U => G x.val) = q := by
        funext x
        simp only [G, dif_neg x.property]
      change Continuous (fun x : U => G x.val)
      rw [heq]
      exact q.continuous
    have hG : Continuous G := by
      apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x ∈ A
      · have hGx : G x = f ⟨x, hx⟩ := by simp only [G, dif_pos hx]
        change Tendsto G (𝓝 x) (𝓝 (G x))
        rw [hGx]
        apply tendsto_iff_dist_tendsto_zero.mpr
        have hbound : ∀ y, dist (G y) (f ⟨x, hx⟩) ≤ 3 * dist y x := by
          intro y
          by_cases hy : y ∈ A
          · rw [show G y = f ⟨y, hy⟩ by simp only [G, dif_pos hy],
              hf.dist_eq, Subtype.dist_eq]
            nlinarith [dist_nonneg (x := y) (y := x)]
          · have h := Set.mem_iInter.mp (hq ⟨y, hy⟩) ⟨x, hx⟩
            simpa only [G, dif_neg hy, t, mem_closedBall] using h
        have hlimit : Tendsto (fun y : H => 3 * dist y x) (𝓝 x) (𝓝 0) := by
          have hc : Continuous (fun y : H => 3 * dist y x) :=
            continuous_const.mul (continuous_id.dist continuous_const)
          simpa only [dist_self, mul_zero] using hc.tendsto x
        exact squeeze_zero (fun y => dist_nonneg) hbound hlimit
      · exact hGoff.continuousAt (hA.isOpen_compl.mem_nhds hx)
    refine ⟨⟨G, hG⟩, ?_⟩
    intro a
    simp only [ContinuousMap.coe_mk, G, dif_pos a.property]
  · have hempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, ?_⟩
    intro a
    exact False.elim (by simpa only [hempty, mem_empty_iff_false] using a.property)

end SurveyStatements.P4
