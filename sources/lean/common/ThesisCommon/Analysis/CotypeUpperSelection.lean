import ThesisCommon.Analysis.CotypeOperators
import ThesisCommon.Analysis.InfiniteFusion
import ThesisCommon.Analysis.CZeroSingles
import ThesisCommon.Analysis.SequenceCoordinates
import Mathlib.Data.Fin.Embedding
import Mathlib.Analysis.SpecificLimits.Basic

/-! Forward nested-set selection for UPFP Proposition 3.5.
Finite cotype selects a column at each stage; the infinite-set recursion keeps
all previously obtained entries small on every later selected coordinate.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The recursive cotype selection for any concrete family of disjoint
coordinate insertions and uniformly bounded output rows. -/
theorem HasFiniteCotype.upper_entry_selection (h : HasFiniteCotype X)
    (J : ℕ → Y →L[𝕜] Z)
    (hJ : ∀ n (e : Fin n ↪ ℕ) (x : Fin n → Y), (∀ i, ‖x i‖ ≤ 1) →
      ∀ θ : Fin n → Bool, ‖∑ i, if θ i then J (e i) (x i) else -(J (e i) (x i))‖ ≤ 1)
    (row : ℕ → Z →L[𝕜] X) {M : ℝ} (hM : 0 ≤ M) (hrow : ∀ m, ‖row m‖ ≤ M)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ i j, i < j →
      ‖(row (e j)).comp (J (e i))‖ < δ i := by
  classical
  obtain ⟨q, C, h⟩ := h
  have step : ∀ k (A : Set ℕ), A.Infinite → ∃ n ∈ A, ∃ B : Set ℕ,
      B.Infinite ∧ B ⊆ A ∧ (∀ m ∈ B, n < m) ∧
      (∀ m ∈ B, ‖(row m).comp (J n)‖ < δ k) := by
    intro k A hA
    obtain ⟨N, hN⟩ := exists_cotype_power_threshold (q := q) (C := C) (M := M) (hδ k)
    let a : Fin N ↪ ℕ := (Fin.valEmbedding.trans (hA.natEmbedding A)).trans
      (Function.Embedding.subtype A)
    let b := Finset.univ.sup (fun i : Fin N => a i)
    let L : Set ℕ := {m ∈ A | b < m}
    have hL : L.Infinite := infinite_above hA b
    let e : ℕ ↪ ℕ := (hL.natEmbedding L).trans (Function.Embedding.subtype L)
    have hs : ∀ m : ℕ, ∃ i : Fin N, ‖(row (e m)).comp (J (a i))‖ < δ k := by
      intro m
      exact h.exists_small_block_power (fun i => J (a i)) (hJ N a) (row (e m))
        (hδ k) hM (hrow (e m)) hN
    choose i hi using hs
    obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber i
    have hj' : (i ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
    refine ⟨a j, (hA.natEmbedding A j).property, e '' (i ⁻¹' {j}),
      (Set.infinite_image_iff e.injective.injOn).mpr hj', ?_, ?_, ?_⟩
    · rintro m ⟨r, _, rfl⟩
      exact (hL.natEmbedding L r).property.1
    · rintro m ⟨r, _, rfl⟩
      exact (Finset.le_sup (f := fun s : Fin N => a s) (Finset.mem_univ j)).trans_lt
        (hL.natEmbedding L r).property.2
    · rintro m ⟨r, hr, rfl⟩
      have heq : i r = j := hr
      simpa only [heq] using hi r
  obtain ⟨f, hf, _, hsmall⟩ := infinite_fusion_entries
    (fun k n m => ‖(row m).comp (J n)‖ < δ k)
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) step
  exact ⟨⟨f, hf.injective⟩, hf, hsmall⟩

theorem infinity_single_embedding_sign_bound {n : ℕ} (e : Fin n ↪ ℕ)
    (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ 1) (θ : Fin n → Bool) :
    ‖∑ i, if θ i then lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ (e i) (x i)
      else -(lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ (e i) (x i))‖ ≤ 1 := by
  apply infinity_norm_sign_sum_le _ _ _ θ
  · intro i
    simpa only [lp.singleContinuousLinearMap_apply, lp.norm_single (by simp : (0 : ℝ≥0∞) < ∞)] using hx i
  · intro i j hij k
    by_cases hk : k = e i
    · subst k
      right
      have hne : e i ≠ e j := fun heq => hij (e.injective heq)
      simp [lp.singleContinuousLinearMap_apply, hne]
    · left
      simp [lp.singleContinuousLinearMap_apply, hk]

/-- The complete upper entry-selection recursion for operators on ℓ∞(X). -/
theorem HasFiniteCotype.infinity_upper_selection (h : HasFiniteCotype X)
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ i j, i < j →
      ‖((lpCoordinate ∞ (e j)).comp T).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ (e i))‖ < δ i := by
  have hrow : ∀ m : ℕ, ‖(lpCoordinate (𝕜 := 𝕜) (X := X) ∞ m).comp T‖ ≤ ‖T‖ := by
    intro m
    calc
      _ ≤ ‖lpCoordinate (𝕜 := 𝕜) (X := X) ∞ m‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_lpCoordinate_le ∞ m) (norm_nonneg T)
      _ = ‖T‖ := one_mul _
  exact h.upper_entry_selection (𝕜 := 𝕜) (Y := X) (Z := EllInfinitySum X)
    (fun n => lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ n)
    (fun n e x hx θ => infinity_single_embedding_sign_bound (𝕜 := 𝕜) e x hx θ)
    (fun m => (lpCoordinate ∞ m).comp T) (norm_nonneg T) hrow δ hδ

/-- The complete upper entry-selection recursion for operators on c₀(X). -/
theorem HasFiniteCotype.cZero_upper_selection (h : HasFiniteCotype X)
    (T : CZeroSum X →L[𝕜] CZeroSum X)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ i j, i < j →
      ‖((cZeroCoordinate (e j)).comp T).comp (cZeroSingleCLM (e i))‖ < δ i := by
  have hrow : ∀ m : ℕ, ‖(cZeroCoordinate (𝕜 := 𝕜) (X := X) m).comp T‖ ≤ ‖T‖ := by
    intro m
    calc
      _ ≤ ‖cZeroCoordinate (𝕜 := 𝕜) (X := X) m‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_cZeroCoordinate_le m) (norm_nonneg T)
      _ = ‖T‖ := one_mul _
  exact h.upper_entry_selection (𝕜 := 𝕜) (Y := X) (Z := CZeroSum X) (cZeroSingleCLM (𝕜 := 𝕜))
    (fun n e x hx θ => cZero_single_embedding_sign_bound (𝕜 := 𝕜) e x hx θ)
    (fun m => (cZeroCoordinate m).comp T) (norm_nonneg T) hrow δ hδ

end ThesisCommon
