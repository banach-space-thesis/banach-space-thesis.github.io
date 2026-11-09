import PL1.StrongConvergence

noncomputable section
open Filter
open scoped Topology

namespace PL1CD

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

theorem exists_strongLimit_of_dense
    (T : ℕ → E →L[𝕜] F) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖T n‖ ≤ C)
    (D : Set E) (hD : Dense D) (hseq : ∀ x ∈ D, CauchySeq (fun n => T n x)) :
    ∃ L : E →L[𝕜] F, ‖L‖ ≤ C ∧ ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (L x)) := by
  have hdist (n : ℕ) (x y : E) : dist (T n x) (T n y) ≤ C * dist x y := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact ((T n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
  have hcauchy (x : E) : CauchySeq (fun n => T n x) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hden : 0 < 4 * (C + 1) := by positivity
    obtain ⟨y, hyD, hxy⟩ := Metric.mem_closure_iff.mp (hD x)
      (ε / (4 * (C + 1))) (div_pos hε hden)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hseq y hyD) (ε / 2) (by positivity)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hy := hN m hm n hn
    have hb : dist (T m x) (T n x) ≤
        C * dist x y + dist (T m y) (T n y) + C * dist x y := by
      calc
        _ ≤ dist (T m x) (T m y) + dist (T m y) (T n x) := dist_triangle _ _ _
        _ ≤ dist (T m x) (T m y) +
            (dist (T m y) (T n y) + dist (T n y) (T n x)) :=
          add_le_add le_rfl (dist_triangle _ _ _)
        _ ≤ C * dist x y + (dist (T m y) (T n y) + C * dist y x) :=
          add_le_add (hdist m x y) (add_le_add le_rfl (hdist n y x))
        _ = _ := by rw [dist_comm y x]; ring
    have hx := (lt_div_iff₀ hden).mp hxy
    nlinarith [dist_nonneg (x := x) (y := y)]
  choose L hL using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  have hadd (x y : E) : L (x + y) = L x + L y := by
    exact tendsto_nhds_unique (hL (x + y))
      (by simpa only [map_add] using (hL x).add (hL y))
  have hsmul (c : 𝕜) (x : E) : L (c • x) = c • L x := by
    exact tendsto_nhds_unique (hL (c • x))
      (by simpa only [map_smul] using (hL x).const_smul c)
  let lin : E →ₗ[𝕜] F := { toFun := L, map_add' := hadd, map_smul' := hsmul }
  have hn (x : E) : ‖lin x‖ ≤ C * ‖x‖ :=
    le_of_tendsto ((hL x).norm) (Eventually.of_forall (fun n =>
      ((T n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg x))))
  let clm := lin.mkContinuous C hn
  exact ⟨clm, clm.opNorm_le_bound hC hn, hL⟩

end PL1CD
