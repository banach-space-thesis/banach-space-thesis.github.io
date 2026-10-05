import ThesisCommon.Analysis.SchauderOperators

/-! A concrete Schauder-basis criterion used for enumerating product bases.
Dense algebraic span and contractive finite coordinate projections imply
convergence of the ordered expansions. No completeness or convergence is
assumed in this criterion.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Uniformly contractive coordinate projections converge to the identity
when their biorthogonal vectors have dense span. -/
theorem schauder_expansion_of_dense_span (v : ℕ → X) (c : ℕ → X →L[𝕜] 𝕜)
    (hvc : ∀ i j, c i (v j) = if i = j then 1 else 0)
    (hd : DenseRange (Submodule.span 𝕜 (Set.range v)).subtypeL)
    (hp : ∀ (F : Finset ℕ) (x : X), ‖∑ n ∈ F, c n x • v n‖ ≤ ‖x‖)
    (x : X) : Tendsto (fun N => ∑ n ∈ Finset.range N, c n x • v n) atTop (𝓝 x) := by
  classical
  let P (N : ℕ) : X →L[𝕜] X := ∑ n ∈ Finset.range N, (c n).smulRight (v n)
  have hP (N : ℕ) (z : X) : P N z = ∑ n ∈ Finset.range N, c n z • v n := by
    simp only [P, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  have hv (i N : ℕ) (hi : i < N) : P N (v i) = v i := by
    rw [hP]
    simp [hvc, Finset.mem_range.mpr hi]
  have hf (z : X) (hz : z ∈ Submodule.span 𝕜 (Set.range v)) :
      ∃ N, ∀ m, N ≤ m → P m z = z := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨i + 1, fun m hm => hv i m (by omega)⟩
    | zero => exact ⟨0, fun _ _ => map_zero _⟩
    | add z w _ _ hz hw =>
      obtain ⟨N, hN⟩ := hz
      obtain ⟨M, hM⟩ := hw
      refine ⟨max N M, fun m hm => ?_⟩
      rw [map_add, hN m ((le_max_left _ _).trans hm), hM m ((le_max_right _ _).trans hm)]
    | smul a z _ hz =>
      obtain ⟨N, hN⟩ := hz
      exact ⟨N, fun m hm => by rw [map_smul, hN m hm]⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨z, ⟨w, rfl⟩, hw⟩ := Metric.mem_closure_iff.mp (hd x) (ε / 3) (by positivity)
  change dist x (w : X) < ε / 3 at hw
  obtain ⟨N, hN⟩ := hf w w.property
  refine ⟨N, ?_⟩
  intro m hm
  rw [← hP, dist_eq_norm]
  have hid : P m x - x = P m (x - w) + (w - x) := by
    rw [map_sub, hN m hm]
    abel
  calc
    ‖P m x - x‖ = ‖P m (x - w) + (w - x)‖ := congrArg norm hid
    _ ≤ ‖P m (x - w)‖ + ‖(w : X) - x‖ := norm_add_le _ _
    _ ≤ ‖x - w‖ + ‖(w : X) - x‖ := add_le_add_right (by rw [hP]; exact hp _ _) _
    _ = 2 * dist x w := by rw [norm_sub_rev (w : X) x, dist_eq_norm]; ring
    _ < ε := by linarith

/-- Construct the actual normalized basis from its vectors and coordinates. -/
def schauderBasisOfDenseSpan (v : ℕ → X) (c : ℕ → X →L[𝕜] 𝕜)
    (hvc : ∀ i j, c i (v j) = if i = j then 1 else 0)
    (hv : ∀ i, ‖v i‖ = 1)
    (hd : DenseRange (Submodule.span 𝕜 (Set.range v)).subtypeL)
    (hp : ∀ (F : Finset ℕ) (x : X), ‖∑ n ∈ F, c n x • v n‖ ≤ ‖x‖) :
    NormalizedSchauderBasis 𝕜 X where
  vector := v
  coord := c
  biorthogonal := hvc
  norm_vector := hv
  expansion := schauder_expansion_of_dense_span v c hvc hd hp

end ThesisCommon
