import ThesisCommon.Analysis.UncountableSchauderScalarisation
import ThesisCommon.Analysis.UncountableSchauderCountableSupport
import ThesisCommon.Analysis.CountableCoordinateSupport

/-! Separable scalar ranges and countable coordinate-block support.
The proof uses the union of the supports of the coordinate insertions,
followed by convergence of the genuine finite-subset expansion.
-/
noncomputable section
open Filter Topology TopologicalSpace
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 Γ E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

omit [CompleteSpace E] in
/-- The dense-set argument of Lemma 4.13, applied directly to the original
scalar basis space. -/
theorem NormalizedSchauderFamily.separable_countable_support
    (b : NormalizedSchauderFamily 𝕜 Γ E) {s : Set E} (hs : IsSeparable s) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x ∈ s, ∀ γ ∉ Λ, b.coord γ x = 0 := by
  obtain ⟨Λ, hΛ, h⟩ := separable_countable_coordinate_support
    (fun x γ => b.coord γ x) (fun γ => (b.coord γ).continuous)
    b.countable_coord_support hs
  refine ⟨Λ, hΛ, ?_⟩
  intro x hx γ hγ
  by_contra hn
  exact hγ (h x hx hn)

namespace UncountableSchauderSum
variable {b : NormalizedSchauderFamily 𝕜 Γ E} {hb : b.IsOneUnconditional}

/-- Operators from X to E(Γ,X) have countable support whenever all scalar
operators from X to E have separable range. -/
theorem operator_countable_support_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] E, IsSeparable (Set.range S))
    (T : X →L[𝕜] UncountableSchauderSum b hb X) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : X, ∀ γ ∉ Λ, T x γ = 0 := by
  apply operator_countable_support_of_scalar (T := T)
  intro S
  obtain ⟨Λ, hΛ, h⟩ := b.separable_countable_support (hsep S)
  exact ⟨Λ, hΛ, fun x => h (S x) ⟨x, rfl⟩⟩

/-- Lemma 4.15: the union over a countable input block of the supports of
T composed with each canonical insertion controls the entire input block.
The last step takes the limit of finite coordinate sums in the actual norm. -/
theorem countable_block_support_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] E, IsSeparable (Set.range S))
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (Δ : Set Γ) (hΔ : Δ.Countable) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : UncountableSchauderSum b hb X,
      (∀ γ ∉ Δ, x γ = 0) → ∀ γ ∉ Λ, T x γ = 0 := by
  classical
  have hα (α : Γ) := operator_countable_support_of_separable_scalar_ranges hsep
    (T.comp (singleL (b := b) (hb := hb) (Y := X) α))
  choose A hA hTA using hα
  let Λ : Set Γ := ⋃ α ∈ Δ, A α
  refine ⟨Λ, hΔ.biUnion (fun α _ => hA α), ?_⟩
  intro x hx γ hγ
  let R : UncountableSchauderSum b hb X →L[𝕜] X := (coordinate γ).comp T
  have hz (α : Γ) : R (single α (x α)) = 0 := by
    by_cases hαΔ : α ∈ Δ
    · have hγα : γ ∉ A α := by
        intro hm
        exact hγ (Set.mem_iUnion.mpr ⟨α, Set.mem_iUnion.mpr ⟨hαΔ, hm⟩⟩)
      simpa only [R, ContinuousLinearMap.comp_apply, singleL_apply]
        using hTA α (x α) γ hγα
    · have hzero : single (b := b) (hb := hb) α (x α) = 0 := by
        ext i
        simp [single_apply, hx α hαΔ]
      rw [hzero, map_zero]
  have ht := (R.continuous.tendsto x).comp (expansion x)
  have hs : Tendsto (fun F : Finset Γ => R (∑ α ∈ F, single α (x α)))
      atTop (𝓝 0) := by
    simpa only [map_sum, hz, Finset.sum_const_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Finset Γ => (0 : X)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hs

/-- The separable alternative of Corollary 4.16, with the same countable
coordinate-block conclusion as Lemma 4.15. -/
theorem countable_block_support_of_separable [SeparableSpace X]
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (Δ : Set Γ) (hΔ : Δ.Countable) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : UncountableSchauderSum b hb X,
      (∀ γ ∉ Δ, x γ = 0) → ∀ γ ∉ Λ, T x γ = 0 :=
  countable_block_support_of_separable_scalar_ranges
    (fun S => isSeparable_range S.continuous) T Δ hΔ

end UncountableSchauderSum
end ThesisCommon
