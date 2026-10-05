import ThesisCommon.Analysis.EllOneSelfSimilarSmallBlocks
import ThesisCommon.Analysis.SequenceBlockTailBounds
import ThesisCommon.Analysis.InfiniteFusionParameters
import Mathlib.Data.Fin.Embedding

/-! UPFP Proposition 4.5: each retained future column carries an inner
infinite set. Refining that set preserves the estimates at every earlier row. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem ellOne_backward_selection (J : (ℕ ↪ ℕ) → X →L[𝕜] X)
    (hJ : ∀ a, ‖J a‖ ≤ 1)
    (hcomp : ∀ a b, (J a).comp (J b) = J (b.trans a))
    (hnorm : ∀ (S : X →L[𝕜] Y) (a b : ℕ ↪ ℕ), Set.range b ⊆ Set.range a →
      ‖S.comp (J b)‖ ≤ ‖S.comp (J a)‖)
    (hback : ∀ (ε M : ℝ), 0 < ε → 0 ≤ M → ∃ N : ℕ,
      ∀ S : X →L[𝕜] EllOneSum (Fin N) Y, ‖S‖ ≤ M →
        ∃ (i : Fin N) (a : ℕ ↪ ℕ), ‖((lpCoordinate 1 i).comp S).comp (J a)‖ < ε)
    (T : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ Y) (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ i j, i < j →
      ‖((lpCoordinate 1 (e i)).comp
        (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 (e j)))).comp (J (a j))‖ < δ i := by
  classical
  let col := fun n => T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 n)
  let r : (ℕ ↪ ℕ) → (ℕ ↪ ℕ) → Prop := fun b a => Set.range b ⊆ Set.range a
  let Q : ℕ → ℕ → ℕ → (ℕ ↪ ℕ) → Prop := fun k n m b =>
    ‖((lpCoordinate 1 n).comp (col m)).comp (J b)‖ < δ k
  have hmono : ∀ k n m a b, r b a → Q k n m a → Q k n m b := by
    intro k n m a b hba hsmall
    exact (hnorm ((lpCoordinate 1 n).comp (col m)) a b hba).trans_lt hsmall
  have step : ∀ k (A : Set ℕ), A.Infinite → ∀ b : ℕ → (ℕ ↪ ℕ),
      ∃ n ∈ A, ∃ (B : Set ℕ) (c : ℕ → (ℕ ↪ ℕ)), B.Infinite ∧ B ⊆ A ∧
        (∀ m ∈ B, n < m) ∧ (∀ m, r (c m) (b m)) ∧ (∀ m ∈ B, Q k n m (c m)) := by
    intro k A hA b
    obtain ⟨N, hN⟩ := hback (δ k) ‖T‖ (hδ k) (norm_nonneg T)
    let a : Fin N ↪ ℕ := (Fin.valEmbedding.trans (hA.natEmbedding A)).trans
      (Function.Embedding.subtype A)
    let upper := Finset.univ.sup (fun i : Fin N => a i)
    let L : Set ℕ := {m ∈ A | upper < m}
    have hL : L.Infinite := infinite_above hA upper
    let e : ℕ ↪ ℕ := (hL.natEmbedding L).trans (Function.Embedding.subtype L)
    let S : ℕ → X →L[𝕜] EllOneSum (Fin N) Y := fun m =>
      ((lpRestrict 1 a).comp (col m)).comp (J (b m))
    have hs : ∀ m, ∃ (i : Fin N) (d : ℕ ↪ ℕ),
        ‖((lpCoordinate 1 i).comp (S m)).comp (J d)‖ < δ k := by
      intro m
      apply hN (S m)
      apply (norm_comp_right_contraction _ _ (hJ (b m))).trans
      apply (norm_lpRestrict_comp_le (col m) a).trans
      exact norm_comp_right_contraction T _ (norm_lpSingleCLM_le m)
    choose i d hi using hs
    obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber (fun s => i (e s))
    have hj' : ((fun s => i (e s)) ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
    let c : ℕ → (ℕ ↪ ℕ) := fun m => (d m).trans (b m)
    refine ⟨a j, (hA.natEmbedding A j).property,
      e '' ((fun s => i (e s)) ⁻¹' {j}), c,
      (Set.infinite_image_iff e.injective.injOn).mpr hj', ?_, ?_, ?_, ?_⟩
    · rintro m ⟨s, _, rfl⟩
      exact (hL.natEmbedding L s).property.1
    · rintro m ⟨s, _, rfl⟩
      exact (Finset.le_sup (f := fun t : Fin N => a t) (Finset.mem_univ j)).trans_lt
        (hL.natEmbedding L s).property.2
    · intro m
      rintro n ⟨t, rfl⟩
      exact ⟨d m t, rfl⟩
    · rintro m ⟨s, hs, rfl⟩
      have heq : i (e s) = j := hs
      have hsmall := hi (e s)
      rw [heq] at hsmall
      change ‖((lpCoordinate 1 (a j)).comp (col (e s))).comp
        ((J (b (e s))).comp (J (d (e s))))‖ < δ k at hsmall
      rw [hcomp] at hsmall
      exact hsmall
  obtain ⟨f, a, hf, _hmem, hsmall⟩ := infinite_fusion_parameters r
    (fun _ => Set.Subset.rfl) (fun _ _ _ h₁ h₂ => h₁.trans h₂) Q hmono
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
    (fun _ => Function.Embedding.refl ℕ) step
  exact ⟨⟨f, hf.injective⟩, a, hf, hsmall⟩

/-- Uniform choice of finite width for every allowed lp inner exponent. -/
theorem lp_ellOne_backward_width (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p = ∞ ∨ 1 < p.toReal)
    {ε M : ℝ} (hε : 0 < ε) (_hM : 0 ≤ M) : ∃ N : ℕ,
    ∀ S : lp (fun _ : ℕ => X) p →L[𝕜] EllOneSum (Fin N) Y, ‖S‖ ≤ M →
      ∃ (i : Fin N) (a : ℕ ↪ ℕ), ‖((lpCoordinate 1 i).comp S).comp (lpExtend p a)‖ < ε := by
  rcases hp with rfl | hp
  · obtain ⟨N, hN⟩ := exists_nat_gt (2 * M / ε)
    refine ⟨N, fun S hS => infinity_to_ellOne_backward_reduction S hε ?_⟩
    exact (mul_le_mul_of_nonneg_left hS (by norm_num)).trans_lt ((div_lt_iff₀ hε).mp hN)
  · obtain ⟨N, hN⟩ := exists_ellOne_power_threshold (M := M) hp hε
    refine ⟨N, fun S hS => lp_to_ellOne_backward_reduction p hp S hε ?_⟩
    exact (mul_le_mul_of_nonneg_left hS (by norm_num)).trans_lt hN

/-- Proposition 4.5 for all lp inner spaces in its scope. -/
theorem ellOne_lp_backward_selection (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p = ∞ ∨ 1 < p.toReal)
    (T : EllOneSum ℕ (lp (fun _ : ℕ => X) p) →L[𝕜] EllOneSum ℕ (lp (fun _ : ℕ => X) p))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ i j, i < j →
      ‖((lpCoordinate 1 (e i)).comp
        (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => lp (fun _ : ℕ => X) p) 1 (e j)))).comp
          (lpExtend p (a j))‖ < δ i := by
  exact ellOne_backward_selection (𝕜 := 𝕜)
    (X := lp (fun _ : ℕ => X) p) (Y := lp (fun _ : ℕ => X) p)
    (fun a => lpExtend (𝕜 := 𝕜) (X := X) p a) (fun a => norm_lpExtend_le a)
    (fun a b => lpExtend_comp b a) norm_comp_lpExtend_le_of_range_subset
    (fun _ _ hε hM => lp_ellOne_backward_width (𝕜 := 𝕜) (X := X)
      (Y := lp (fun _ : ℕ => X) p) p hp hε hM) T δ hδ

/-- Proposition 4.5 for c₀ inner spaces. -/
theorem ellOne_cZero_backward_selection
    (T : EllOneSum ℕ (CZeroSum X) →L[𝕜] EllOneSum ℕ (CZeroSum X))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ i j, i < j →
      ‖((lpCoordinate 1 (e i)).comp
        (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => CZeroSum X) 1 (e j)))).comp
          (cZeroExtend (a j))‖ < δ i := by
  apply ellOne_backward_selection (𝕜 := 𝕜) (X := CZeroSum X) (Y := CZeroSum X)
    (fun a => cZeroExtend (𝕜 := 𝕜) (X := X) a) (fun a => norm_cZeroExtend_le a)
    (fun a b => cZeroExtend_comp b a) norm_comp_cZeroExtend_le_of_range_subset _ T δ hδ
  intro ε M hε _hM
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * M / ε)
  refine ⟨N, fun S hS => cZero_to_ellOne_backward_reduction S hε ?_⟩
  exact (mul_le_mul_of_nonneg_left hS (by norm_num)).trans_lt ((div_lt_iff₀ hε).mp hN)

end ThesisCommon

