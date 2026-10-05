import ThesisCommon.Analysis.IntervalSmallBlocks
import ThesisCommon.Analysis.IntervalChains
import ThesisCommon.Analysis.InfiniteFusionParameters

/-! LPCK 4.3 for the unit interval. At each stage the retained output
copies are further restricted. Finite chains of normalized interval maps
record genuine nested closed copies and preserve every earlier estimate. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem interval_upper_entry_selection
    (J : ℕ → X →L[𝕜] Y)
    (hJ : ∀ N (a : Fin N ↪ ℕ) (x : Fin N → X),
      (∀ i, ‖x i‖ ≤ 1) → ‖∑ i, J (a i) (x i)‖ ≤ 1)
    (row : ℕ → Y →L[𝕜] IntervalContinuous 𝕜)
    {M : ℝ} (hrow : ∀ m, ‖row m‖ ≤ M) (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → IntervalChain), StrictMono e ∧ ∀ i j, i < j →
      ‖((intervalChainRead (a j)).comp (row (e j))).comp (J (e i))‖ ≤ δ i := by
  classical
  let Q : ℕ → ℕ → ℕ → IntervalChain → Prop := fun k n m a =>
    ‖((intervalChainRead a).comp (row m)).comp (J n)‖ ≤ δ k
  have hmono : ∀ k n m a b, b.Refines a → Q k n m a → Q k n m b := by
    intro k n m a b hba hs
    change ‖((intervalChainRead b).comp (row m)).comp (J n)‖ ≤ δ k
    rw [ContinuousLinearMap.comp_assoc]
    apply (norm_intervalChainRead_comp_le_of_refines ((row m).comp (J n)) hba).trans
    simpa only [ContinuousLinearMap.comp_assoc] using hs
  have step : ∀ k (A : Set ℕ), A.Infinite → ∀ b : ℕ → IntervalChain,
      ∃ n ∈ A, ∃ (B : Set ℕ) (c : ℕ → IntervalChain), B.Infinite ∧ B ⊆ A ∧
        (∀ m ∈ B, n < m) ∧ (∀ m, (c m).Refines (b m)) ∧ (∀ m ∈ B, Q k n m (c m)) := by
    intro k A hA b
    obtain ⟨N, hN⟩ := exists_nat_gt (M / δ k)
    have hlarge : M < (N : ℝ) * δ k := (div_lt_iff₀ (hδ k)).mp hN
    let a : Fin N ↪ ℕ := (Fin.valEmbedding.trans (hA.natEmbedding A)).trans
      (Function.Embedding.subtype A)
    let upper := Finset.univ.sup (fun i : Fin N => a i)
    let L : Set ℕ := {m ∈ A | upper < m}
    have hL : L.Infinite := infinite_above hA upper
    let e : ℕ ↪ ℕ := (hL.natEmbedding L).trans (Function.Embedding.subtype L)
    have hs : ∀ m : ℕ, ∃ (i : Fin N) (d : NondegenerateUnitSubinterval),
        ‖((intervalRead d).comp ((intervalChainRead (b m)).comp (row m))).comp (J (a i))‖ ≤ δ k := by
      intro m
      apply interval_exists_small_block (fun i => J (a i)) (hJ N a) _ (hδ k).le
        ((norm_comp_left_contraction (intervalChainRead (𝕜 := 𝕜) (b m))
          (norm_intervalChainRead_le (𝕜 := 𝕜) (b m)) (row m)).trans (hrow m)) hlarge
    choose i d hi using hs
    obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber (fun s => i (e s))
    have hj' : ((fun s => i (e s)) ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
    let c : ℕ → IntervalChain := fun m => d m :: b m
    refine ⟨a j, (hA.natEmbedding A j).property, e '' ((fun s => i (e s)) ⁻¹' {j}), c,
      (Set.infinite_image_iff e.injective.injOn).mpr hj', ?_, ?_, ?_, ?_⟩
    · rintro m ⟨s, _, rfl⟩
      exact (hL.natEmbedding L s).property.1
    · rintro m ⟨s, _, rfl⟩
      exact (Finset.le_sup (f := fun t : Fin N => a t) (Finset.mem_univ j)).trans_lt
        (hL.natEmbedding L s).property.2
    · intro m
      exact ⟨[d m], rfl⟩
    · rintro m ⟨s, hs, rfl⟩
      have heq : i (e s) = j := hs
      have hsmall := hi (e s)
      rw [heq] at hsmall
      simpa only [Q, c, intervalChainRead, ContinuousLinearMap.comp_assoc] using hsmall
  obtain ⟨f, a, hf, _, hs⟩ := infinite_fusion_parameters IntervalChain.Refines
    IntervalChain.Refines.refl (fun _ _ _ h₁ h₂ => h₁.trans h₂) Q hmono
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) (fun _ => []) step
  exact ⟨⟨f, hf.injective⟩, a, hf, hs⟩

theorem interval_infinity_upper_selection
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum (IntervalContinuous 𝕜))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → IntervalChain), StrictMono e ∧ ∀ i j, i < j →
      ‖((intervalChainRead (a j)).comp ((lpCoordinate ∞ (e j)).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ (e i))‖ ≤ δ i := by
  apply interval_upper_entry_selection
    (fun i => lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ i) ?_
    (fun m => (lpCoordinate ∞ m).comp T)
    (fun m => norm_comp_left_contraction _ (norm_lpCoordinate_le ∞ m) T) δ hδ
  intro N a x hx
  simpa using infinity_single_embedding_sign_bound (𝕜 := 𝕜) a x hx (fun _ => true)

end ThesisCommon
