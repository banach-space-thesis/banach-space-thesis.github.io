import ThesisCommon.Analysis.UncountableSchauderBasis
import ThesisCommon.Analysis.CZeroArbitrarySingles

/-! The actual normalized symmetric c₀ family over any discrete index type.
Its expansion is the norm-convergent net of finite coordinate sections.
-/
noncomputable section
open Filter Topology
open scoped ZeroAtInfty BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ : Type*} [RCLike 𝕜] [TopologicalSpace Γ] [DiscreteTopology Γ]

theorem cZeroSingleAt_smul_unit (γ : Γ) (a : 𝕜) :
    a • cZeroSingleAt γ (1 : 𝕜) = cZeroSingleAt γ a := by
  ext δ
  by_cases h : δ = γ <;> simp [h]

def scalarCZeroSchauderFamily : NormalizedSchauderFamily 𝕜 Γ C₀(Γ, 𝕜) where
  vector γ := cZeroSingleAt γ 1
  coord := cZeroCoordinate
  biorthogonal i j := by simp
  norm_vector i := by
    apply le_antisymm
    · simpa using norm_cZeroSingleAt_le i (1 : 𝕜)
    · simpa using BoundedContinuousFunction.norm_coe_le_norm
        (cZeroSingleAt i (1 : 𝕜)).toBCF i
  expansion x := by
    simpa only [cZeroCoordinate_apply, cZeroSingleAt_smul_unit] using
      cZero_hasSum_singleAt (𝕜 := 𝕜) x

theorem scalarCZeroSchauderFamily_oneUnconditional :
    (scalarCZeroSchauderFamily (𝕜 := 𝕜) (Γ := Γ)).IsOneUnconditional := by
  let b := scalarCZeroSchauderFamily (𝕜 := 𝕜) (Γ := Γ)
  refine ⟨le_rfl, ?_⟩
  intro F a c hac
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro i
  change ‖b.coord i (∑ γ ∈ F, a γ • b.vector γ)‖ ≤ _
  rw [b.coord_finite_sum]
  by_cases hi : i ∈ F
  · rw [if_pos hi]
    apply (hac i hi).trans
    have h := BoundedContinuousFunction.norm_coe_le_norm
      (∑ γ ∈ F, c γ • b.vector γ).toBCF i
    change ‖b.coord i (∑ γ ∈ F, c γ • b.vector γ)‖ ≤ _ at h
    simpa only [b.coord_finite_sum, if_pos hi] using h
  · simp [hi]

theorem scalarCZeroExtend_norm_arbitrary (e : Γ ↪ Γ) (x : C₀(Γ, 𝕜)) :
    ‖cZeroExtend (𝕜 := 𝕜) e x‖ = ‖x‖ := by
  apply le_antisymm (norm_cZeroInsert_le e x)
  have h := norm_cZeroRead_le e (cZeroExtend (𝕜 := 𝕜) e x)
  have heq : cZeroRead e (cZeroExtend (𝕜 := 𝕜) e x) = x := by
    ext γ
    exact cZeroExtend_apply_image (𝕜 := 𝕜) e x γ
  simpa only [heq] using h

theorem cZeroExtend_singleAt (e : Γ ↪ Γ) (γ : Γ) (a : 𝕜) :
    cZeroExtend (𝕜 := 𝕜) e (cZeroSingleAt γ a) = cZeroSingleAt (e γ) a := by
  ext δ
  by_cases hδ : δ ∈ Set.range e
  · obtain ⟨η, rfl⟩ := hδ
    rw [cZeroExtend_apply_image]
    simp only [cZeroSingleAt_apply, e.injective.eq_iff]
  · have hδγ : δ ≠ e γ := fun heq => hδ ⟨γ, heq.symm⟩
    simp [cZeroExtend, cZeroInsert, Function.extend_apply' _ _ _ hδ, hδγ]

theorem scalarCZeroSchauderFamily_symmetric :
    (scalarCZeroSchauderFamily (𝕜 := 𝕜) (Γ := Γ)).HasSymmetricNorm := by
  refine ⟨scalarCZeroSchauderFamily_oneUnconditional, ?_⟩
  intro σ F a
  have h := scalarCZeroExtend_norm_arbitrary σ.toEmbedding
    (∑ γ ∈ F, a γ • cZeroSingleAt γ (1 : 𝕜))
  simpa only [map_sum, map_smul, cZeroExtend_singleAt, Equiv.toEmbedding_apply] using h

theorem cZero_norm_finite_units_le_one_arbitrary (F : Finset Γ) :
    ‖∑ γ ∈ F, cZeroSingleAt γ (1 : 𝕜)‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro γ
  change ‖(∑ α ∈ F, cZeroSingleAt α (1 : 𝕜)) γ‖ ≤ 1
  rw [cZero_finite_singleAt_apply (𝕜 := 𝕜)]
  split_ifs <;> simp

theorem scalarCZeroSchauderFamily_not_equivalentEllOne [Infinite Γ] :
    ¬ (scalarCZeroSchauderFamily (𝕜 := 𝕜) (Γ := Γ)).EquivalentEllOne := by
  rintro ⟨c, hc, h⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
  obtain ⟨F, hF⟩ := Finset.exists_card_eq (α := Γ) N
  have hh := h F (fun _ => 1)
  simp only [norm_one, Finset.sum_const, hF, nsmul_eq_mul, mul_one,
    one_smul, scalarCZeroSchauderFamily] at hh
  have hu := cZero_norm_finite_units_le_one_arbitrary (𝕜 := 𝕜) F
  have : 1 < c * N := by
    have := (div_lt_iff₀ hc).mp hN
    nlinarith
  exact (not_lt_of_ge (hh.trans hu)) this

end ThesisCommon
