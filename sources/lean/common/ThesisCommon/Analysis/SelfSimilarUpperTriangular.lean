import ThesisCommon.Analysis.SelfSimilarUpperSelection
import ThesisCommon.Analysis.CotypeUpperTriangular

/-! The complete upper selection and row-sum estimate of UPFP Proposition 3.8,
for both c₀ and infinity, on the actual finite-p coefficient space.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem infinity_lp_upper_selection (hp : p ≠ ∞)
    (T : EllInfinitySum (lp (fun _ : ℕ => X) p) →L[𝕜]
      EllInfinitySum (lp (fun _ : ℕ => X) p))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ i j, i < j →
      ‖((lpRestrict p (a j)).comp ((lpCoordinate ∞ (e j)).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => lp (fun _ : ℕ => X) p) ∞ (e i))‖ < δ i := by
  apply lp_upper_entry_selection p hp
    (fun n => lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => lp (fun _ : ℕ => X) p) ∞ n)
    (fun n e x hx θ => infinity_single_embedding_sign_bound (𝕜 := 𝕜) e x hx θ)
    (fun n => (lpCoordinate ∞ n).comp T) (norm_nonneg T) _ δ hδ
  intro m
  calc
    _ ≤ ‖lpCoordinate (𝕜 := 𝕜) (X := lp (fun _ : ℕ => X) p) ∞ m‖ * ‖T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_lpCoordinate_le ∞ m) (norm_nonneg T)
    _ = _ := one_mul _

theorem cZero_lp_upper_selection (hp : p ≠ ∞)
    (T : CZeroSum (lp (fun _ : ℕ => X) p) →L[𝕜] CZeroSum (lp (fun _ : ℕ => X) p))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ i j, i < j →
      ‖((lpRestrict p (a j)).comp ((cZeroCoordinate (e j)).comp T)).comp
        (cZeroSingleCLM (e i))‖ < δ i := by
  apply lp_upper_entry_selection (𝕜 := 𝕜) (X := X)
    (Y := lp (fun _ : ℕ => X) p) (Z := CZeroSum (lp (fun _ : ℕ => X) p)) p hp
    (cZeroSingleCLM (𝕜 := 𝕜) (X := lp (fun _ : ℕ => X) p))
    (fun n e x hx θ => cZero_single_embedding_sign_bound (𝕜 := 𝕜) e x hx θ)
    (fun n => (cZeroCoordinate n).comp T) (norm_nonneg T) _ δ hδ
  intro m
  calc
    _ ≤ ‖cZeroCoordinate (𝕜 := 𝕜) (X := lp (fun _ : ℕ => X) p) m‖ * ‖T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_cZeroCoordinate_le m) (norm_nonneg T)
    _ = _ := one_mul _

/-- Proposition 3.8, infinity case, with one retained inner set for each row. -/
theorem infinity_lp_upper_triangular (hp : p ≠ ∞)
    (T : EllInfinitySum (lp (fun _ : ℕ => X) p) →L[𝕜]
      EllInfinitySum (lp (fun _ : ℕ => X) p)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ j,
      (∑ i ∈ Finset.range j, ‖((lpRestrict p (a j)).comp ((lpCoordinate ∞ (e j)).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => lp (fun _ : ℕ => X) p) ∞ (e i))‖) < ε := by
  obtain ⟨e, a, hmono, he⟩ := infinity_lp_upper_selection p hp T
    (fun k => (ε / 4) * (1 / 2 : ℝ) ^ k) (fun k => by positivity)
  exact ⟨e, a, hmono, sum_lt_of_geometric_entries hε _ he⟩

/-- Proposition 3.8, c₀ case, using genuine bounded coordinate maps. -/
theorem cZero_lp_upper_triangular (hp : p ≠ ∞)
    (T : CZeroSum (lp (fun _ : ℕ => X) p) →L[𝕜] CZeroSum (lp (fun _ : ℕ => X) p))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ j,
      (∑ i ∈ Finset.range j, ‖((lpRestrict p (a j)).comp ((cZeroCoordinate (e j)).comp T)).comp
        (cZeroSingleCLM (e i))‖) < ε := by
  obtain ⟨e, a, hmono, he⟩ := cZero_lp_upper_selection p hp T
    (fun k => (ε / 4) * (1 / 2 : ℝ) ^ k) (fun k => by positivity)
  exact ⟨e, a, hmono, sum_lt_of_geometric_entries hε _ he⟩

end ThesisCommon
