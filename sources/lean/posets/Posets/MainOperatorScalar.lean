import Posets.MainOperatorReduction
import Posets.AcceptanceDichotomyMatrixAlgebra
import Posets.CanonicalEmbedding

/-! The ordered and unordered operator conclusions once the construction has
provided scalar-shift admission outside countable exceptional families. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 ℬ : Set (Set ℕ)}

/-- An uncountable source-only family forces the scalar in self-admission to vanish. -/
theorem scalar_eq_zero_of_self_admission (h𝒜 : IsAlmostDisjoint 𝒜)
    (hbig : IsAlmostDisjoint (𝒜 ∪ ℬ)) (hdiff : ¬ (𝒜 \ ℬ).Countable)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (a : 𝕜) (𝒜' : Set (Set ℕ)) (hcount : 𝒜'.Countable)
    (hself : Admits 𝕜 (𝒜 \ 𝒜') (𝒜 \ 𝒜') (reducedMatrix 𝕜 T - a • identityMatrix 𝕜)) :
    a = 0 := by
  let D := 𝒜' ∪ Subtype.val '' operatorExceptionalFamily h𝒜 T
  have hD : D.Countable := hcount.union ((operatorExceptionalFamily_countable h𝒜 T).image _)
  have hex : ∃ A ∈ 𝒜 \ ℬ, A ∉ D := by
    by_contra hn
    push_neg at hn
    exact hdiff (hD.mono hn)
  obtain ⟨A, ⟨hAA, hAB⟩, hAD⟩ := hex
  let A₀ : 𝒜 := ⟨A, hAA⟩
  have hAE : A₀ ∉ operatorExceptionalFamily h𝒜 T := fun h => hAD (Or.inr ⟨A₀, h, rfl⟩)
  have hA' : A ∉ 𝒜' := fun h => hAD (Or.inl h)
  have hins : IsAlmostDisjoint (insert A ℬ) := by
    have hs : insert A ℬ ⊆ 𝒜 ∪ ℬ := by
      intro B hB
      rcases hB with rfl | hB
      · exact Or.inl hAA
      · exact Or.inr hB
    exact ⟨fun B hB => hbig.1 B (hs hB),
      fun B hB C hC hBC => hbig.2 B (hs hB) C (hs hC) hBC⟩
  have hzero : Tendsto (matrixAction 𝕜 (reducedMatrix 𝕜 T) (indicator 𝕜 A)) (Along A) (𝓝 0) := by
    have h := (zero_at_infty (T (familyVector 𝕜 𝒜 h𝒜 A₀))).comp
      (natural_tendsto_cocompact hAB hins)
    exact h.congr (operator_family_matrix h𝒜 T A₀ hAE)
  have hM : HasBoundedRows 𝕜 (reducedMatrix 𝕜 T) :=
    ⟨reducedMatrix_row_summable T, ‖T‖, reducedMatrix_row_bound T⟩
  have hshift (k : ℕ) :
      matrixAction 𝕜 (reducedMatrix 𝕜 T - a • identityMatrix 𝕜) (indicator 𝕜 A) k =
        matrixAction 𝕜 (reducedMatrix 𝕜 T) (indicator 𝕜 A) k - a * indicator 𝕜 A k := by
    have hf : (⇑(naturalRestriction 𝒜 (familyVector 𝕜 𝒜 h𝒜 A₀)) : ℕ → 𝕜) =
        indicator 𝕜 A := funext (fun n => familyVector_natural 𝕜 𝒜 h𝒜 A₀ n)
    have hs := matrixAction_scalarShift hM a
      (naturalRestriction 𝒜 (familyVector 𝕜 𝒜 h𝒜 A₀)) k
    rwa [hf] at hs
  have hscalar : Tendsto (matrixAction 𝕜 (reducedMatrix 𝕜 T) (indicator 𝕜 A)) (Along A) (𝓝 a) := by
    have hs := (hself A ⟨hAA, hA'⟩ A ⟨hAA, hA'⟩).add_const a
    simp only [zero_add] at hs
    apply hs.congr'
    filter_upwards [eventually_mem_along A] with k hk
    rw [hshift]
    simp [indicator, hk]
  letI : NeBot (Along A) := (h𝒜.1 A hAA).cofinite_inf_principal_neBot
  exact tendsto_nhds_unique hscalar hzero

theorem operator_decomposition_of_admission (h𝒜 : IsAlmostDisjoint 𝒜)
    (hℬ : IsAlmostDisjoint ℬ) (hsub : 𝒜 ⊆ ℬ) (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ)
    (a : 𝕜) (𝒜' ℬ' : Set (Set ℕ)) (hAcount : 𝒜'.Countable) (hBcount : ℬ'.Countable)
    (hcross : Admits 𝕜 (𝒜 \ 𝒜') (ℬ \ ℬ') (reducedMatrix 𝕜 T - a • identityMatrix 𝕜)) :
    ∃ S : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ, FactorsThroughCZero 𝕜 S ∧
      T = a • (canonicalEmbedding hsub hℬ).toContinuousLinearMap + S := by
  refine ⟨T - a • (canonicalEmbedding hsub hℬ).toContinuousLinearMap, ?_, ?_⟩
  · apply factorsThroughCZero_of_admission h𝒜 hℬ _ 𝒜' ℬ' hAcount hBcount
    simpa only [reducedMatrix_sub, reducedMatrix_smul, reducedMatrix_canonicalEmbedding] using hcross
  · abel

theorem offOrder_factorization_of_admission (h𝒜 : IsAlmostDisjoint 𝒜)
    (hℬ : IsAlmostDisjoint ℬ) (hbig : IsAlmostDisjoint (𝒜 ∪ ℬ))
    (hdiff : ¬ (𝒜 \ ℬ).Countable) (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ)
    (a : 𝕜) (𝒜' ℬ' : Set (Set ℕ)) (hAcount : 𝒜'.Countable) (hBcount : ℬ'.Countable)
    (hself : Admits 𝕜 (𝒜 \ 𝒜') (𝒜 \ 𝒜') (reducedMatrix 𝕜 T - a • identityMatrix 𝕜))
    (hcross : Admits 𝕜 (𝒜 \ 𝒜') (ℬ \ ℬ') (reducedMatrix 𝕜 T - a • identityMatrix 𝕜)) :
    FactorsThroughCZero 𝕜 T := by
  have ha := scalar_eq_zero_of_self_admission h𝒜 hbig hdiff T a 𝒜' hAcount hself
  apply factorsThroughCZero_of_admission h𝒜 hℬ T 𝒜' ℬ' hAcount hBcount
  simpa only [ha, zero_smul, sub_zero] using hcross

end Posets
