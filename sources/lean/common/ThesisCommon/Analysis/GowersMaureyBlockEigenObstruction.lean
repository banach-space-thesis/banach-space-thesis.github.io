import ThesisCommon.Analysis.GowersMaureyStrictlySingularSubspaces

/-! Summably accurate scalar eigenvectors on actual successive finite
blocks give a lower bound on their full infinite-dimensional scalar span. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem not_strictlySingular_of_block_eigen_errors (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (a : 𝕜) (ha : a ≠ 0)
    (u : ℕ → C00 𝕜) (hu : ∀ i j, i < j → Before (u i) (u j))
    (hun : ∀ i, implicitNorm D (u i) = 1)
    (η : ℕ → ℝ) (hη : ∀ i, 0 ≤ η i)
    (herr : ∀ i, ‖T (denseEmbedding D (u i))-a • denseEmbedding D (u i)‖ ≤ η i)
    (hsum : ∀ s : Finset ℕ, ∑ i ∈ s, η i ≤ ‖a‖/4) :
    ¬ IsStrictlySingularOperator T := by
  classical
  let v := fun i => denseEmbedding D (u i)
  have hcoeff : ∀ s : Finset ℕ, ∀ c : ℕ → 𝕜, ∀ i ∈ s,
      ‖c i‖ ≤ 2*‖∑ j ∈ s, c j • v j‖ := by
    intro s c i hi
    have hh := scalar_block_coefficient_le_twice D hu s c hi
      (by rw [hun i]; norm_num : (1 : ℝ)/2 ≤ implicitNorm D (u i))
    have hn : ‖∑ j ∈ s, c j • v j‖ = implicitNorm D (∑ j ∈ s, c j • u j) := by
      change ‖∑ j ∈ s, c j • denseEmbedding D (u j)‖ = _
      simp_rw [← map_smul]
      rw [← map_sum, denseEmbedding_norm]
      rfl
    rwa [hn]
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
    have hli : LinearIndependent 𝕜 (fun i => (⟨v i,hvF i⟩ : F)) := by
      apply LinearIndependent.of_comp F.subtype
      exact hlin
    letI := hli.finite
    exact not_finite ℕ
  have herror : ∀ x : F, ‖T x.val-a • x.val‖ ≤ (‖a‖/2)*‖x.val‖ := by
    intro x
    obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp x.property
    have hx : x.val = ∑ i ∈ c.support, c i • v i := hc.symm
    have he : T (∑ i ∈ c.support, c i • v i)-a • (∑ i ∈ c.support, c i • v i) =
        ∑ i ∈ c.support, c i • (T (v i)-a • v i) := by
      simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, smul_comm a,
        Finset.sum_sub_distrib]
    rw [hx, he]
    calc
      _ ≤ ∑ i ∈ c.support, ‖c i • (T (v i)-a • v i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ c.support, (2*‖∑ j ∈ c.support, c j • v j‖)*η i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left (herr i) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (hcoeff _ _ i hi) (hη i))
      _ = (2*‖∑ j ∈ c.support, c j • v j‖)*∑ i ∈ c.support, η i :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (2*‖∑ j ∈ c.support, c j • v j‖)*(‖a‖/4) :=
        mul_le_mul_of_nonneg_left (hsum _) (by positivity)
      _ = _ := by ring
  intro hT
  apply hF
  apply hT F
  refine ⟨‖a‖/2, div_pos (norm_pos_iff.mpr ha) (by norm_num), ?_⟩
  intro x
  change (‖a‖/2)*‖x.val‖ ≤ ‖T x.val‖
  have hh := norm_le_insert' (a • x.val) (T x.val)
  rw [norm_smul, norm_sub_rev] at hh
  have he := herror x
  linarith

end ThesisCommon.GowersMaurey
