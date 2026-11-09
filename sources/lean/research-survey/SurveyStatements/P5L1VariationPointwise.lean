import SurveyStatements.P5L1VariationLimit

/-! Concrete dyadic symbol functions converge pointwise inside the interval.
Each point determines a genuine nested dyadic branch. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

def stepSymbol (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (n : ℕ) (x : ℝ) : 𝕜 :=
  ∑ k : Fin (2 ^ n), (lpHaarCell n k).indicator (fun _ => d n k) x

theorem stepSymbol_on_cell (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (n : ℕ)
    (k : Fin (2 ^ n)) {x : ℝ} (hx : x ∈ lpHaarCell n k) :
    stepSymbol 𝕜 d n x = d n k := by
  unfold stepSymbol
  rw [Finset.sum_eq_single k]
  · simp [hx]
  · intro j _ hjk
    have hj : x ∉ lpHaarCell n j := fun h =>
      Set.disjoint_left.mp (lpHaarLevelCells_disjoint n hjk) h hx
    simp [hj]
  · simp

theorem stepSymbol_norm_le (𝕜 : Type*) [RCLike 𝕜]
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
    (n : ℕ) (x : ℝ) : ‖stepSymbol 𝕜 d n x‖ ≤ ‖D‖ := by
  by_cases h : ∃ k : Fin (2 ^ n), x ∈ lpHaarCell n k
  · obtain ⟨k, hk⟩ := h
    rw [stepSymbol_on_cell 𝕜 d n k hk]
    exact multiplier_symbol_norm_le 𝕜 D d hD n k
  · have hs : stepSymbol 𝕜 d n x = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact Set.indicator_of_notMem (fun hk => h ⟨k, hk⟩) _
    rw [hs, norm_zero]
    exact norm_nonneg _

def pointIndex (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) (j : ℕ) : Fin (2 ^ (0 + j)) :=
  Classical.choose (show ∃ k : Fin (2 ^ (0 + j)), x ∈ lpHaarCell (0 + j) k from
    mem_iUnion.mp (by rw [lpHaarLevelCells_union]; exact hx))

theorem pointIndex_mem (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) (j : ℕ) :
    x ∈ lpHaarCell (0 + j) (pointIndex x hx j) :=
  Classical.choose_spec (show ∃ k : Fin (2 ^ (0 + j)), x ∈ lpHaarCell (0 + j) k from
    mem_iUnion.mp (by rw [lpHaarLevelCells_union]; exact hx))

def pointBranch (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) : DyadicBranch 0 where
  index := pointIndex x hx
  parent := by
    intro j
    let q := pointIndex x hx (j + 1)
    let p := lpHaarParentIndex (0 + j) q
    have hxq := pointIndex_mem x hx (j + 1)
    have hxp : x ∈ lpHaarCell (0 + j) p := by
      rw [← lpHaarCell_children]
      have hq : q.val = 2 * p.val ∨ q.val = 2 * p.val + 1 := by
        dsimp [p, lpHaarParentIndex]
        omega
      rcases hq with h | h
      · apply Or.inl
        simpa only [q, ← h] using hxq
      · apply Or.inr
        simpa only [q, ← h] using hxq
    by_contra h
    exact Set.disjoint_left.mp (lpHaarLevelCells_disjoint (0 + j) h)
      hxp (pointIndex_mem x hx j)

theorem stepSymbol_pointwise_exists_limit (𝕜 : Type*) [RCLike 𝕜]
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
    (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    ∃ c : 𝕜, Tendsto (fun n => stepSymbol 𝕜 d n x) atTop (𝓝 c) ∧ ‖c‖ ≤ ‖D‖ := by
  let B := pointBranch x hx
  obtain ⟨c, hc⟩ := B.symbol_exists_limit 𝕜 D d hD
  have he : (fun n => stepSymbol 𝕜 d n x) = B.symbol 𝕜 d := by
    funext n
    have h := stepSymbol_on_cell 𝕜 d (0 + n) (B.index n) (pointIndex_mem x hx n)
    simpa only [Nat.zero_add, DyadicBranch.symbol] using h
  rw [← he] at hc
  exact ⟨c, hc, le_of_tendsto hc.norm (Eventually.of_forall
    (fun n => stepSymbol_norm_le 𝕜 D d hD n x))⟩

end SurveyStatements.P5L1Variation
