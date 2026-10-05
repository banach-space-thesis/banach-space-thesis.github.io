import ThesisCommon.Analysis.GowersMaureyStrictlySingularBlocks
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Actual infinite-dimensional small subspaces for strictly singular
operators on the constructed shift space. Summable gliding-hump errors
control every scalar linear combination, not merely the selected vectors. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem scalar_block_sum_perturbation_le (D : ConstructionData 𝕜)
    (u : ℕ → C00 𝕜) (v : ℕ → ShiftSpace D)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hun : ∀ i, (1 : ℝ)/2 ≤ implicitNorm D (u i))
    (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (he : ∀ i, ‖denseEmbedding D (u i)-v i‖ ≤ ε i)
    (s : Finset ℕ) (c : ℕ → 𝕜) :
    ‖denseEmbedding D (∑ i ∈ s, c i • u i) - ∑ i ∈ s, c i • v i‖ ≤
      (2 * implicitNorm D (∑ i ∈ s, c i • u i)) * ∑ i ∈ s, ε i := by
  rw [map_sum]
  simp_rw [map_smul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, ‖c i • denseEmbedding D (u i)-c i • v i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖c i‖ * ‖denseEmbedding D (u i)-v i‖ := by
      simp only [← smul_sub, norm_smul]
    _ ≤ ∑ i ∈ s, (2 * implicitNorm D (∑ j ∈ s, c j • u j)) * ε i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (mul_le_mul_of_nonneg_left (he i) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right
          (scalar_block_coefficient_le_twice D hu s c hi (hun i)) (hε i))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem perturbed_scalar_block_coefficient_le_four (D : ConstructionData 𝕜)
    (u : ℕ → C00 𝕜) (v : ℕ → ShiftSpace D)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hun : ∀ i, (1 : ℝ)/2 ≤ implicitNorm D (u i))
    (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (he : ∀ i, ‖denseEmbedding D (u i)-v i‖ ≤ ε i)
    (s : Finset ℕ) (c : ℕ → 𝕜) (hs : ∑ i ∈ s, ε i ≤ 1/4)
    {i : ℕ} (hi : i ∈ s) : ‖c i‖ ≤ 4 * ‖∑ j ∈ s, c j • v j‖ := by
  have hp := scalar_block_sum_perturbation_le D u v hu hun ε hε he s c
  have hb := scalar_block_coefficient_le_twice D hu s c hi (hun i)
  have ht := norm_le_insert' (denseEmbedding D (∑ j ∈ s, c j • u j))
    (∑ j ∈ s, c j • v j)
  rw [denseEmbedding_norm] at ht
  change implicitNorm D (∑ j ∈ s, c j • u j) ≤
    ‖∑ j ∈ s, c j • v j‖ +
      ‖denseEmbedding D (∑ j ∈ s, c j • u j)-∑ j ∈ s, c j • v j‖ at ht
  have hh := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2 * implicitNorm D (∑ j ∈ s, c j • u j) by positivity)
  nlinarith

theorem strictlySingular_exists_infinite_small_subspace (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (hT : IsStrictlySingularOperator T)
    (E : Submodule 𝕜 (ShiftSpace D)) (hE : ¬ FiniteDimensional 𝕜 E)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : Submodule 𝕜 (ShiftSpace D), F ≤ E ∧ ¬ FiniteDimensional 𝕜 F ∧
      ∀ x : F, ‖T x.val‖ ≤ δ * ‖x.val‖ := by
  classical
  let ε : ℕ → ℝ := fun i => (1/8 : ℝ) * ((1 : ℝ)/2)^i
  let η : ℕ → ℝ := fun i => (δ/8) * ((1 : ℝ)/2)^i
  have hε : ∀ i, 0 < ε i := fun i => mul_pos (by norm_num) (pow_pos (by norm_num) i)
  have hη : ∀ i, 0 < η i := fun i => mul_pos (by positivity) (pow_pos (by norm_num) i)
  have hεanti : Antitone ε := by
    apply antitone_nat_of_succ_le
    intro i
    dsimp only [ε]
    rw [pow_succ]
    have hh : 0 ≤ (1/8 : ℝ) * ((1 : ℝ)/2)^i := (hε i).le
    nlinarith
  have hηanti : Antitone η := by
    apply antitone_nat_of_succ_le
    intro i
    dsimp only [η]
    rw [pow_succ]
    have hh : 0 ≤ (δ/8) * ((1 : ℝ)/2)^i := (hη i).le
    nlinarith
  obtain ⟨u,v,hu,hvE,_,herr,hun,hvT⟩ :=
    exists_strictlySingular_block_sequence D T hT E hE ε η hε hη hεanti hηanti
  have hsε : HasSum ε (1/4) := by
    convert hasSum_geometric_two.mul_left (1/8 : ℝ) using 1
    norm_num
  have hsη : HasSum η (δ/4) := by
    convert hasSum_geometric_two.mul_left (δ/8) using 1
    ring
  have hsumε : ∀ s : Finset ℕ, ∑ i ∈ s, ε i ≤ 1/4 := fun s =>
    (hsε.summable.sum_le_tsum s (fun i _ => (hε i).le)).trans_eq hsε.tsum_eq
  have hsumη : ∀ s : Finset ℕ, ∑ i ∈ s, η i ≤ δ/4 := fun s =>
    (hsη.summable.sum_le_tsum s (fun i _ => (hη i).le)).trans_eq hsη.tsum_eq
  have hcoeff : ∀ s : Finset ℕ, ∀ c : ℕ → 𝕜, ∀ i ∈ s,
      ‖c i‖ ≤ 4 * ‖∑ j ∈ s, c j • v j‖ := fun s c i hi =>
    perturbed_scalar_block_coefficient_le_four D u v hu hun ε (fun i => (hε i).le)
      (fun i => (herr i).le) s c (hsumε s) hi
  let F := Submodule.span 𝕜 (Set.range v)
  have hvF : ∀ i, v i ∈ F := fun i => Submodule.subset_span ⟨i,rfl⟩
  have hlin : LinearIndependent 𝕜 v := by
    apply linearIndependent_iff'.mpr
    intro s c hz i hi
    apply norm_eq_zero.mp
    have hh := hcoeff s c i hi
    rw [hz, norm_zero, mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)
  have hF : ¬ FiniteDimensional 𝕜 F := by
    intro hfin
    letI := hfin
    have hli : LinearIndependent 𝕜 (fun i => (⟨v i, hvF i⟩ : F)) := by
      apply LinearIndependent.of_comp F.subtype
      exact hlin
    letI := hli.finite
    exact not_finite ℕ
  refine ⟨F, Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hvE i), hF, ?_⟩
  intro x
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp x.property
  have hx : x.val = ∑ i ∈ c.support, c i • v i := hc.symm
  rw [hx, map_sum]
  simp_rw [map_smul]
  calc
    _ ≤ ∑ i ∈ c.support, ‖c i • T (v i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ c.support, ‖c i‖ * ‖T (v i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i ∈ c.support, (4 * ‖∑ j ∈ c.support, c j • v j‖) * η i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (mul_le_mul_of_nonneg_left (hvT i).le (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hcoeff _ _ i hi) (hη i).le)
    _ = (4 * ‖∑ j ∈ c.support, c j • v j‖) * ∑ i ∈ c.support, η i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (4 * ‖∑ j ∈ c.support, c j • v j‖) * (δ/4) :=
      mul_le_mul_of_nonneg_left (hsumη _) (by positivity)
    _ = _ := by ring

end ThesisCommon.GowersMaurey
