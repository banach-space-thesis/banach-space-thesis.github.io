import ThesisCommon.Analysis.SchauderOperators

/-! Construct a bounded infinite operator from uniformly bounded finite
operators that eventually stabilise on each basis vector. Convergence on
the whole Banach space follows from density and an explicit norm estimate. -/

noncomputable section
open Filter Set Topology
open scoped BigOperators
namespace ThesisCommon.NormalizedSchauderBasis
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

theorem exists_operator_of_stable_basis (b : NormalizedSchauderBasis 𝕜 X)
    (P : ℕ → X →L[𝕜] Y) {C : ℝ} (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hstable : ∀ j, ∃ N, ∀ n ≥ N, P n (b.vector j) = P N (b.vector j)) :
    ∃ A : X →L[𝕜] Y, ‖A‖ ≤ C ∧
      ∀ x, Tendsto (fun n => P n x) atTop (𝓝 (A x)) := by
  choose N hN using hstable
  let v : ℕ → Y := fun j => P (N j) (b.vector j)
  have hv (j : ℕ) : Tendsto (fun n => P n (b.vector j)) atTop (𝓝 (v j)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (N j)] with n hn
    exact (hN j n hn).symm
  have hsum (F : Finset ℕ) (a : ℕ → 𝕜) :
      Tendsto (fun n => P n (∑ j ∈ F, a j • b.vector j)) atTop
        (𝓝 (∑ j ∈ F, a j • v j)) := by
    simp only [map_sum, map_smul]
    exact tendsto_finset_sum F (fun j _ => (hv j).const_smul (a j))
  have hnorm (F : Finset ℕ) (a : ℕ → 𝕜) :
      ‖∑ j ∈ F, a j • v j‖ ≤ C * ‖∑ j ∈ F, a j • b.vector j‖ := by
    apply le_of_tendsto (hsum F a).norm
    exact Eventually.of_forall (fun n => ((P n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hP n) (norm_nonneg _)))
  obtain ⟨A, hA, hAv⟩ := b.exists_operator v hC hnorm
  have hspan (x : X) (hx : x ∈ Submodule.span 𝕜 (Set.range b.vector)) :
      Tendsto (fun n => P n x) atTop (𝓝 (A x)) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      simpa only [hAv] using hv j
    | zero => simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Y)) atTop (𝓝 0))
    | add x y _ _ hx hy => simpa only [map_add] using hx.add hy
    | smul c x _ hx => simpa only [map_smul] using hx.const_smul c
  refine ⟨A, hA, fun x => Metric.tendsto_atTop.mpr (fun ε hε => ?_)⟩
  obtain ⟨y, hy⟩ := b.dense_span.exists_dist_lt x
    (div_pos hε (by linarith : 0 < 3 * (C + 1)))
  have hlim := hspan y y.property
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim (ε / 3) (by linarith)
  refine ⟨M, fun n hn => ?_⟩
  have hPdist : dist (P n x) (P n y) ≤ C * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((P n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hP n) (norm_nonneg _))
  have hAdist : dist (A y) (A x) ≤ C * dist x y := by
    rw [dist_comm (A y), dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hsmall : C * dist x y < ε / 3 := by
    have hmul := (mul_lt_mul_of_pos_right hy (by linarith : 0 < 3 * (C + 1)))
    rw [div_mul_cancel₀ _ (by linarith : 3 * (C + 1) ≠ 0)] at hmul
    change dist x (y : X) * (3 * (C + 1)) < ε at hmul
    have hdist : 0 ≤ dist x (y : X) := dist_nonneg
    nlinarith [hdist]
  calc
    dist (P n x) (A x) ≤ dist (P n x) (P n y) +
        (dist (P n y) (A y) + dist (A y) (A x)) := by
          simpa only [add_assoc] using dist_triangle4 (P n x) (P n y) (A y) (A x)
    _ < ε := by linarith [hM n hn]

end ThesisCommon.NormalizedSchauderBasis
