import ThesisCommon.Analysis.SelfSimilarSmallBlocks
import ThesisCommon.Analysis.InfiniteFusionParameters
import ThesisCommon.Analysis.SequenceRestrictionAlgebra
import Mathlib.Data.Fin.Embedding

/-! The simultaneous inner-coordinate recursion of UPFP Proposition 3.8.
Each retained row carries an injective enumeration of its current inner set.
At every stage these sets are refined, so all earlier estimates persist.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Choose outer coordinates and one inner set per chosen row. The signed
input bound is supplied by the actual disjoint insertions for each sum. -/
theorem lp_upper_entry_selection (hp : p ≠ ∞)
    (J : ℕ → Y →L[𝕜] Z)
    (hJ : ∀ n (e : Fin n ↪ ℕ) (x : Fin n → Y), (∀ i, ‖x i‖ ≤ 1) →
      ∀ θ : Fin n → Bool, ‖∑ i, if θ i then J (e i) (x i) else -(J (e i) (x i))‖ ≤ 1)
    (row : ℕ → Z →L[𝕜] lp (fun _ : ℕ => X) p)
    {M : ℝ} (hM : 0 ≤ M) (hrow : ∀ m, ‖row m‖ ≤ M)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ i j, i < j →
      ‖((lpRestrict p (a j)).comp (row (e j))).comp (J (e i))‖ < δ i := by
  classical
  let r : (ℕ ↪ ℕ) → (ℕ ↪ ℕ) → Prop := fun b a => Set.range b ⊆ Set.range a
  let Q : ℕ → ℕ → ℕ → (ℕ ↪ ℕ) → Prop := fun k n m b =>
    ‖((lpRestrict p b).comp (row m)).comp (J n)‖ < δ k
  have hmono : ∀ k n m a b, r b a → Q k n m a → Q k n m b := by
    intro k n m a b hba hsmall
    change ‖((lpRestrict p b).comp (row m)).comp (J n)‖ < δ k
    rw [ContinuousLinearMap.comp_assoc]
    exact (norm_lpRestrict_comp_le_of_range_subset ((row m).comp (J n)) a b hba).trans_lt hsmall
  have step : ∀ k (A : Set ℕ), A.Infinite → ∀ b : ℕ → (ℕ ↪ ℕ),
      ∃ n ∈ A, ∃ (B : Set ℕ) (c : ℕ → (ℕ ↪ ℕ)), B.Infinite ∧ B ⊆ A ∧
        (∀ m ∈ B, n < m) ∧ (∀ m, r (c m) (b m)) ∧ (∀ m ∈ B, Q k n m (c m)) := by
    intro k A hA b
    obtain ⟨N, hN⟩ := exists_cotype_power_threshold (q := p.toReal) (C := 1) (M := M) (hδ k)
    simp only [Real.one_rpow, one_mul] at hN
    let a : Fin N ↪ ℕ := (Fin.valEmbedding.trans (hA.natEmbedding A)).trans
      (Function.Embedding.subtype A)
    let upper := Finset.univ.sup (fun i : Fin N => a i)
    let L : Set ℕ := {m ∈ A | upper < m}
    have hL : L.Infinite := infinite_above hA upper
    let e : ℕ ↪ ℕ := (hL.natEmbedding L).trans (Function.Embedding.subtype L)
    have hs : ∀ m : ℕ, ∃ i : Fin N,
        ‖((lpRestrict p (disjointCoordinateEmbedding i)).comp
          ((lpRestrict p (b (e m))).comp (row (e m)))).comp (J (a i))‖ < δ k := by
      intro m
      exact lp_exists_small_restricted_block p (finite_exponent_toReal_ge_one p hp)
        (fun i => J (a i)) (hJ N a) ((lpRestrict p (b (e m))).comp (row (e m)))
        (hδ k) hM ((norm_lpRestrict_comp_le (row (e m)) (b (e m))).trans (hrow (e m))) hN
    choose i hi using hs
    obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber i
    have hj' : (i ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
    let c : ℕ → (ℕ ↪ ℕ) := fun m => (disjointCoordinateEmbedding j).trans (b m)
    refine ⟨a j, (hA.natEmbedding A j).property, e '' (i ⁻¹' {j}), c,
      (Set.infinite_image_iff e.injective.injOn).mpr hj', ?_, ?_, ?_, ?_⟩
    · rintro m ⟨s, _, rfl⟩
      exact (hL.natEmbedding L s).property.1
    · rintro m ⟨s, _, rfl⟩
      exact (Finset.le_sup (f := fun t : Fin N => a t) (Finset.mem_univ j)).trans_lt
        (hL.natEmbedding L s).property.2
    · intro m
      rintro n ⟨t, rfl⟩
      exact ⟨disjointCoordinateEmbedding j t, rfl⟩
    · rintro m ⟨s, hs, rfl⟩
      have heq : i s = j := hs
      have hsmall := hi s
      rw [heq] at hsmall
      change ‖((lpRestrict p ((disjointCoordinateEmbedding j).trans (b (e s)))).comp
        (row (e s))).comp (J (a j))‖ < δ k
      simpa only [← lpRestrict_comp, ContinuousLinearMap.comp_assoc] using hsmall
  obtain ⟨f, a, hf, _hmem, hsmall⟩ := infinite_fusion_parameters r
    (fun _ => Set.Subset.rfl) (fun _ _ _ h₁ h₂ => h₁.trans h₂) Q hmono
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
    (fun _ => Function.Embedding.refl ℕ) step
  exact ⟨⟨f, hf.injective⟩, a, hf, hsmall⟩

end ThesisCommon
