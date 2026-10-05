import Posets.SeparableRangeFactorization
import JFA.AmplifiedCompactMinimality
import JFA.AmplifiedXIdeal

/-! Compact minimality and the separable ideal on every Mrówka space.
No few-operators or uncountability hypothesis is used. -/

noncomputable section
open Set Topology ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

/-- A compact operator factors through c₀ with a compact first factor. -/
theorem mrowka_compact_factorization (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) (hT : IsCompactOperator T) :
    ∃ A : Space 𝕜 𝒜 →L[𝕜] cZero 𝕜, ∃ B : cZero 𝕜 →L[𝕜] Space 𝕜 𝒜,
      T = B.comp A ∧ IsCompactOperator A := by
  let X := LinearMap.range T.toLinearMap
  have hX : TopologicalSpace.SeparableSpace X :=
    (JFA.hasSeparableRange_of_isCompactOperator T hT).separableSpace
  obtain ⟨Y, hXY, hYclosed, ⟨e⟩⟩ := lemma_4_4_proof 𝕜 𝒜 h𝒜 X hX
  let hm : ∀ x, T x ∈ Y := fun x => hXY (show T x ∈ X from ⟨x, rfl⟩)
  let T' := T.codRestrict Y hm
  refine ⟨e.toContinuousLinearMap.comp T', Y.subtypeL.comp e.symm.toContinuousLinearMap, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    exact (congrArg Subtype.val (e.symm_apply_apply (T' x))).symm
  · exact (hT.codRestrict hm hYclosed).clm_comp e.toContinuousLinearMap

theorem mrowka_compactOperators_minimal (h𝒜 : IsAlmostDisjoint 𝒜)
    {I : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜)}
    (hI : IsClosedIdeal 𝕜 I) (hIne : I ≠ {0}) :
    {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T} ⊆ I := by
  classical
  have hex : ∃ Q ∈ I, Q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hIne
    apply subset_antisymm
    · intro Q hQ
      exact mem_singleton_iff.mpr (h Q hQ)
    · intro Q hQ
      rw [mem_singleton_iff] at hQ
      exact hQ.symm ▸ hI.2.1
  obtain ⟨Q, hQI, hQ⟩ := hex
  intro T hT
  obtain ⟨A, B, hAB, hc⟩ := mrowka_compact_factorization h𝒜 T hT
  have hclosure : T ∈ closure I := (Metric.mem_closure_iff (s := I) (a := T)).mpr (by
    intro ε hε
    obtain ⟨R, hRI, hR⟩ := JFA.compact_factor_approximant_mem_ideal hI hQI hQ A B hc ε hε
    refine ⟨R, hRI, ?_⟩
    simpa only [hAB, dist_eq_norm] using hR)
  rwa [hI.1.closure_eq] at hclosure

theorem mrowka_compactOperators_ne_zero :
    {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T} ≠ {0} := by
  let v := isolatedVector 𝕜 𝒜 0
  let P := (JLMS.evaluation (𝕜 := 𝕜) (K := Mrowka 𝒜) (Sum.inl 0)).smulRight v
  have hc : IsCompactOperator P := JLMS.isCompactOperator_smulRight _ _
  have hn : P ≠ 0 := by
    intro h
    have he := congrArg (fun T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 => T v (Sum.inl 0)) h
    simp [P, v, ContinuousLinearMap.smulRight_apply] at he
  intro h
  exact hn (mem_singleton_iff.mp (h ▸ hc))

theorem mrowka_noncompact_factors_cZero_identity (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) (hT : ¬ IsCompactOperator T) :
    ∃ U : Space 𝕜 𝒜 →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] Space 𝕜 𝒜,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
  letI := JFA.mrowka_locallyCompactSpace (𝒜 := 𝒜)
  letI := JFA.mrowka_t2Space h𝒜
  have hsc := JFA.mrowka_isScattered (𝒜 := 𝒜)
  obtain ⟨U, V, hUV, _⟩ := JLMS.theorem_1_6_of_scatteredCZero
    (𝕜 := 𝕜) (K := Mrowka 𝒜) (L := Mrowka 𝒜)
    hsc hsc (JLMS.cZero_admissible hsc) T hT 1 zero_lt_one
  exact ⟨U, V, hUV⟩

theorem mrowka_separable_subset_ideal_of_noncompact (h𝒜 : IsAlmostDisjoint 𝒜)
    {I : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜)} (hI : IsClosedIdeal 𝕜 I)
    (hnot : ¬ I ⊆ {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T}) :
    {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | HasSeparableRange 𝕜 _ _ T} ⊆ I := by
  obtain ⟨T, hTI, hT⟩ := Set.not_subset.mp hnot
  obtain ⟨U, V, hUV⟩ := mrowka_noncompact_factors_cZero_identity h𝒜 T hT
  have hf := JFA.factorizationOperators_subset_ideal_of_factors_identity hI hTI U V hUV
  intro S hS
  obtain ⟨A, B, hAB⟩ := factorsThroughCZero_of_hasSeparableRange h𝒜 S hS
  apply hf
  exact Submodule.subset_span ⟨A, B, hAB⟩

theorem mrowka_exists_separable_noncompact (h𝒜 : IsAlmostDisjoint 𝒜) :
    ∃ P : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜,
      HasSeparableRange 𝕜 _ _ P ∧ ¬ IsCompactOperator P := by
  obtain ⟨A, B, hBA⟩ := JFA.mrowka_exists_cZero_retract (𝕜 := 𝕜) h𝒜
  have hr (x : cZero 𝕜) : B (A x) = x := congrArg (fun L => L x) hBA
  let P := A.comp B
  refine ⟨P, (show FactorsThroughCZero 𝕜 P from ⟨B, A, rfl⟩).hasSeparableRange, ?_⟩
  intro hc
  have hci := (hc.comp_clm A).clm_comp B
  have heq : B.comp (P.comp A) = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
    ext x n
    change B (A (B (A x))) n = x n
    rw [hr, hr]
  change IsCompactOperator (B.comp (P.comp A)) at hci
  rw [heq] at hci
  exact JLMS.cZero_not_finiteDimensional 𝕜 (JLMS.finiteDimensional_of_compact_identity hci)

theorem mrowka_strictlyAboveCompact_iff_contains_separable (h𝒜 : IsAlmostDisjoint 𝒜)
    {I : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜)} (hI : IsClosedIdeal 𝕜 I) :
    {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T} ⊂ I ↔
      {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | HasSeparableRange 𝕜 _ _ T} ⊆ I := by
  constructor
  · intro h
    exact mrowka_separable_subset_ideal_of_noncompact h𝒜 hI h.not_subset
  · intro h
    obtain ⟨P, hPs, hPc⟩ := mrowka_exists_separable_noncompact (𝕜 := 𝕜) h𝒜
    refine ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro T hT
      exact h (JFA.hasSeparableRange_of_isCompactOperator T hT)
    · intro heq
      apply hPc
      change P ∈ {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T}
      rw [heq]
      exact h hPs

end Posets
