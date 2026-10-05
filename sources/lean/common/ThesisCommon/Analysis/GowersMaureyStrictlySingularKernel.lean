import ThesisCommon.Analysis.GowersMaureySubspaceBlockSequence
import ThesisCommon.Analysis.GowersMaureyBlockPerturbation
import ThesisCommon.Analysis.GowersMaureyBlockLowerBound
import ThesisCommon.Analysis.GowersMaureyOperatorTargets
import Mathlib.Analysis.SpecificLimits.Basic

/-! Zero block seminorm implies genuine strict singularity on the actual
completed shift space. Arbitrary infinite-dimensional subspaces are reduced
to successive finite blocks by a proved summable-error construction; they
are not assumed to contain finite-support vectors or an exact block basis. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_block_span_near_subspace (D : ConstructionData 𝕜)
    (E : Submodule 𝕜 (ShiftSpace D)) (hE : ¬ FiniteDimensional 𝕜 E)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℕ → C00 𝕜,
      (∀ i j, i < j → Before (u i) (u j)) ∧
      (∀ i, (1 : ℝ)/2 ≤ implicitNorm D (u i)) ∧
      ∀ x ∈ Submodule.span ℝ (Set.range u), ∃ y ∈ E,
        ‖denseEmbedding D x-y‖ ≤ δ * implicitNorm D x := by
  let ε : ℕ → ℝ := fun i => (δ/4) * ((1 : ℝ)/2)^i
  have hε : ∀ i, 0 < ε i := fun i => mul_pos (by positivity) (pow_pos (by norm_num) i)
  have hanti : Antitone ε := by
    apply antitone_nat_of_succ_le
    intro i
    dsimp only [ε]
    rw [pow_succ]
    have hh : 0 ≤ (δ/4) * ((1 : ℝ)/2)^i := (hε i).le
    nlinarith
  obtain ⟨u, v, hu, hvE, _, herr, hunorm⟩ := exists_approximating_block_sequence D E hE ε hε hanti
  have hs : HasSum ε (δ/2) := by
    have hh := hasSum_geometric_two.mul_left (δ/4)
    convert hh using 1
    ring
  have hsum : ∀ s : Finset ℕ, ∑ i ∈ s, ε i ≤ δ/2 := by
    intro s
    exact (hs.summable.sum_le_tsum s (fun i _ => (hε i).le)).trans_eq hs.tsum_eq
  exact ⟨u, hu, hunorm, real_block_span_near_subspace D E u v hu hunorm hvE ε
    (fun i => (hε i).le) (fun i => (herr i).le) hsum⟩

theorem isStrictlySingularOperator_of_spaceOperatorSeminorm_zero
    (D : ConstructionData 𝕜) (T : ShiftSpace D →L[𝕜] ShiftSpace D)
    (hT : spaceOperatorSeminorm D T = 0) : IsStrictlySingularOperator T := by
  intro E hEbound
  obtain ⟨c, hc, hb⟩ := hEbound
  by_contra hE
  let δ := c / (2 * (c + ‖T‖ + 1))
  have hd : 0 < c + ‖T‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hc (mul_pos (by norm_num) hd)
  have hbudget : (c+‖T‖)*δ ≤ c/2 := by
    calc
      _ ≤ (c+‖T‖+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = c/2 := by dsimp only [δ]; field_simp
  obtain ⟨u, hu, hunorm, hnear⟩ := exists_block_span_near_subspace D E hE hδ
  let Y := Submodule.span ℝ (Set.range u)
  have huY : ∀ i, u i ∈ Y := fun i => Submodule.subset_span ⟨i,rfl⟩
  have hne : ∀ i, u i ≠ 0 := by
    intro i hi
    have hh := hunorm i
    rw [hi, map_zero] at hh
    norm_num at hh
  have hblock : ∀ x ∈ Y, (c/2) * implicitNorm D x ≤ ‖T (denseEmbedding D x)‖ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnear x hx
    have hbY : c * ‖y‖ ≤ ‖T y‖ := hb ⟨y,hy⟩
    have hnorm : ‖denseEmbedding D x‖ = implicitNorm D x := denseEmbedding_norm D x
    have hxy' : ‖denseEmbedding D x-y‖ ≤ δ * ‖denseEmbedding D x‖ := by
      rwa [hnorm]
    have ht := lower_bound_transfer_to_near_vector D T hc.le (denseEmbedding D x) y hbY hxy'
    rw [hnorm] at ht
    exact (mul_le_mul_of_nonneg_right (by linarith : c/2 ≤ c-(c+‖T‖)*δ)
      (apply_nonneg _ _)).trans ht
  exact no_block_lower_bound_of_spaceOperatorSeminorm_zero D T hT Y u hu huY hne
    ⟨c/2, by positivity, hblock⟩

end ThesisCommon.GowersMaurey
