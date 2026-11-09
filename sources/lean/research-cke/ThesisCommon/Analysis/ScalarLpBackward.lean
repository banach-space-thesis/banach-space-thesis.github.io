import ThesisCommon.Analysis.ScalarBlockEstimate
import ThesisCommon.Analysis.EllOneThreshold
import ThesisCommon.Analysis.InfiniteFusion
import ThesisCommon.Analysis.SequenceRestrictionAlgebra
import ThesisCommon.Analysis.LpSummableRows
import ThesisCommon.Analysis.SequenceBlockTailBounds
import ThesisCommon.Analysis.DualCotypeDiagonalReduction

/-! The scalar instance of LPCK's backward/lower reduction. Signed disjoint
blocks give a small infinite restriction; fusion then makes the whole future
input of each retained row summably small. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_scalar_backward_reduction {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (hp : 1 < p.toReal) (T : lp (fun _ : ℕ => X) p →L[𝕜] 𝕜)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, ‖T.comp (lpExtend p e)‖ ≤ ε := by
  obtain ⟨N, hN⟩ := exists_ellOne_power_threshold (M := ‖T‖) hp (show 0 < 2*ε by positivity)
  have hlarge : ‖T‖ * (N : ℝ) ^ (1 / p.toReal) < (N : ℝ) * ε := by
    have h := ellOne_power_threshold hp (norm_nonneg T) hN
    convert h using 1; ring
  have hJ : ∀ x : Fin N → lp (fun _ : ℕ => X) p,
      (∀ i, ‖x i‖ ≤ 1) →
      ‖∑ i : Fin N, lpExtend (𝕜 := 𝕜) (X := X) p (disjointCoordinateEmbedding i) (x i)‖ ≤
        (N : ℝ) ^ (1 / p.toReal) := by
    intro x hx
    simpa only [signedValue, if_true] using lp_disjoint_blocks_sign_bound (𝕜 := 𝕜)
      p (zero_lt_one.trans hp) x hx (fun _ => true)
  obtain ⟨i, hi⟩ := exists_small_scalar_block
    (fun i : Fin N => lpExtend (𝕜 := 𝕜) (X := X) p (disjointCoordinateEmbedding i))
    (norm_nonneg T) hJ T le_rfl hlarge
  exact ⟨disjointCoordinateEmbedding i, hi⟩

theorem scalar_lp_backward_selection (hp : 1 < p.toReal)
    (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) p)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ k,
      ‖((lpCoordinate p (e k)).comp T).comp (lpExtend p (coordinateTail e k))‖ ≤ δ k := by
  classical
  let row := fun n => (lpCoordinate p n).comp T
  let Q : ℕ → ℕ → Set ℕ → Prop := fun k n B =>
    ∃ g : ℕ ↪ ℕ, Set.range g = B ∧ ‖(row n).comp (lpExtend p g)‖ ≤ δ k
  have step : ∀ k (A : Set ℕ), A.Infinite → ∃ n ∈ A, ∃ B : Set ℕ,
      B.Infinite ∧ B ⊆ A ∧ (∀ m ∈ B, n < m) ∧ Q k n B := by
    intro k A hA
    obtain ⟨n, hn⟩ := hA.nonempty
    let L := {m ∈ A | n < m}
    have hL : L.Infinite := infinite_above hA n
    let a : ℕ ↪ ℕ := (hL.natEmbedding L).trans (Function.Embedding.subtype L)
    obtain ⟨g, hs⟩ := lp_scalar_backward_reduction hp ((row n).comp (lpExtend p a)) (hδ k)
    refine ⟨n, hn, Set.range (g.trans a), Set.infinite_range_of_injective
      (g.trans a).injective, ?_, ?_, g.trans a, rfl, ?_⟩
    · rintro m ⟨j, rfl⟩
      exact (hL.natEmbedding L (g j)).property.1
    · rintro m ⟨j, rfl⟩
      exact (hL.natEmbedding L (g j)).property.2
    · simpa only [← lpExtend_comp, ContinuousLinearMap.comp_assoc] using hs
  obtain ⟨f, A, _, _, _, _, _, hf, hQ, htail⟩ :=
    infinite_fusion Q (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) step
  let e : ℕ ↪ ℕ := ⟨f, hf.injective⟩
  choose g hg hs using hQ
  refine ⟨e, hf, ?_⟩
  intro k
  apply (norm_comp_lpExtend_le_of_range_subset (row (e k)) (g k) (coordinateTail e k) ?_).trans (hs k)
  rintro m ⟨j, rfl⟩
  rw [hg k]
  exact htail k (k+1+j) (by omega)

theorem scalar_lp_lower_triangular (hp : 1 < p.toReal)
    (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (L : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) p),
      StrictMono e ∧
      ‖((lpRestrict p e).comp T).comp (lpExtend p e) - L‖ < ε ∧
      IsLpLowerPart (((lpRestrict p e).comp T).comp (lpExtend p e)) L := by
  let δ : ℕ → ℝ := fun k => (ε/4) * (1/2 : ℝ)^k
  obtain ⟨e, he, hs⟩ := scalar_lp_backward_selection hp T δ (fun _ => by dsimp [δ]; positivity)
  let S := ((lpRestrict p e).comp T).comp (lpExtend p e)
  have htail : ∀ k, ‖((lpCoordinate p k).comp S).comp
      (lpExtend p (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ δ k := by
    intro k
    have hb := lpBlockCompression_tail_bound p T e
      (fun _ => ContinuousLinearMap.id 𝕜 𝕜) (fun _ => ContinuousLinearMap.id 𝕜 𝕜)
      (fun _ => ContinuousLinearMap.norm_id_le) (fun _ => ContinuousLinearMap.norm_id_le) k
    simp only [lpBlockRead_id, lpBlockInsert_id, ContinuousLinearMap.id_comp] at hb
    exact hb.trans (hs k)
  obtain ⟨L, hL, hpart⟩ := exists_lp_lower_part_of_summable_tails S
    (summable_geometric_two.mul_left (ε/4)) htail
  refine ⟨e, L, he, hL.trans_lt ?_, hpart⟩
  change (∑' k, (ε/4) * (1/2 : ℝ)^k) < ε
  rw [(hasSum_geometric_two.mul_left (ε/4)).tsum_eq]
  linarith

end ThesisCommon
