import ThesisCommon.Analysis.GowersMaureyFiniteNorming
import ThesisCommon.Analysis.GowersMaureyRISRestriction

/-! The actual averaging and special norm tests are forms in the precise
source sense. This links the implicit norm construction to the RIS estimates. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem successive_real_smul {N : ℕ} {x : Fin N → C00 𝕜} (hx : Successive x) (r : ℝ) :
    Successive (fun i => r • x i) := by
  intro i j hij s hs t ht
  exact hx i j hij s (Finsupp.support_smul hs) t (Finsupp.support_smul ht)

theorem pairing_restrict_left (a x : C00 𝕜) (E : Interval) :
    pairing (restrict E a) x = pairing a (restrict E x) := by
  have h : pairing (restrict E a) = (pairing a).comp (restrict E) := by
    apply Finsupp.lhom_ext
    intro n c
    change pairing (restrict E a) (Finsupp.single n c) = pairing a (restrict E (Finsupp.single n c))
    rw [pairing_single, restrict_apply, restrict_single]
    split_ifs <;> simp
  exact LinearMap.congr_fun h x

theorem DualUnit.restrict {D : ConstructionData 𝕜} {a : C00 𝕜}
    (ha : DualUnit (implicitNorm D) a) (E : Interval) : DualUnit (implicitNorm D) (restrict E a) := by
  intro x
  rw [pairing_restrict_left]
  exact (ha _).trans (implicitNorm_restrict_le D E x)

theorem IsForm.restrict {D : ConstructionData 𝕜} {k : ℕ} {weight : ℝ}
    (hw : 0 < weight) {a : C00 𝕜} (ha : IsForm D k weight a) (E : Interval) :
    IsForm D k weight (restrict E a) := by
  obtain ⟨hu, z, hz, hb, heq⟩ := ha
  refine ⟨hu.restrict E, (fun i => GowersMaurey.restrict E (z i)), successive_restrict hz E, ?_, ?_⟩
  · intro i x
    rw [pairing_restrict_left]
    exact (hb i _).trans (mul_le_mul_of_nonneg_left (implicitNorm_restrict_le D E x)
      (inv_nonneg.mpr hw.le))
  · rw [heq, map_sum]

theorem IsForm.of_weight_le {D : ConstructionData 𝕜} {k : ℕ} {v w : ℝ}
    (hv : 0 < v) (hvw : v ≤ w) {a : C00 𝕜} (ha : IsForm D k w a) : IsForm D k v a := by
  obtain ⟨hu, z, hz, hb, heq⟩ := ha
  refine ⟨hu, z, hz, ?_, heq⟩
  intro i x
  exact (hb i x).trans (mul_le_mul_of_nonneg_right
    ((inv_le_inv₀ (hv.trans_le hvw) hv).mpr hvw) (apply_nonneg _ _))

theorem AveragedFunctional.isForm {D : ConstructionData 𝕜} {k : ℕ} {a : C00 𝕜}
    (ha : AveragedFunctional (implicitNorm D) k a) : IsForm D k (logarithmicWeight k) a := by
  have hu := ha.dualUnit
  obtain ⟨hk, z, hz, hb, heq⟩ := ha
  refine ⟨hu, (fun i => (logarithmicWeight k)⁻¹ • z i), successive_real_smul hz _, ?_, ?_⟩
  · intro i x
    rw [pairing_real_smul_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (logarithmicWeight_nonneg k))]
    exact mul_le_mul_of_nonneg_left (hb i x) (inv_nonneg.mpr (logarithmicWeight_nonneg k))
  · simpa only [Finset.smul_sum] using heq

theorem SpecialSequence.specialFunctional_dualUnit (D : ConstructionData 𝕜)
    {k : ℕ} (hk : k ∈ D.specialSizes) {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D (implicitNorm D) g) : DualUnit (implicitNorm D) (specialFunctional g) := by
  intro x
  have h := test_le_implicitNorm D (NormTest.special hk g hg (supportInterval x)) x
  change ‖pairing (specialFunctional g) (restrict (supportInterval x) x)‖ ≤ implicitNorm D x at h
  simpa only [restrict_supportInterval] using h

theorem SpecialSequence.isForm (D : ConstructionData 𝕜) {k : ℕ}
    (hk : k ∈ D.specialSizes) {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D (implicitNorm D) g) :
    IsForm D k (Real.sqrt (logarithmicWeight k)) (specialFunctional g) := by
  refine ⟨hg.specialFunctional_dualUnit D hk,
    (fun i => (Real.sqrt (logarithmicWeight k))⁻¹ • g i), successive_real_smul hg.1 _, ?_, ?_⟩
  · intro i x
    rw [pairing_real_smul_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact mul_le_mul_of_nonneg_left ((hg.2.2 i).dualUnit x)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  · exact Finset.smul_sum

theorem exists_intervalAverage_norming_form (D : ConstructionData 𝕜)
    (T : IntervalTest) (x : C00 𝕜) :
    ∃ a : C00 𝕜, IsForm D T.count (logarithmicWeight T.count) a ∧
      ‖pairing a x‖ = intervalAverage (implicitNorm D) T x := by
  choose z hs hu hn using fun i => exists_finite_interval_norming D (T.interval i) x
  have hz : Successive z := by
    intro i j hij s hsi t htj
    exact T.successive i j hij s (hs i hsi) t (hs j htj)
  let a := (logarithmicWeight T.count)⁻¹ • ∑ i, z i
  have ha : AveragedFunctional (implicitNorm D) T.count a :=
    ⟨by have := T.count_ge_two; omega, z, hz, hu, rfl⟩
  refine ⟨a, ha.isForm, ?_⟩
  rw [intervalAverage_apply]
  change ‖pairing ((logarithmicWeight T.count)⁻¹ • ∑ i, z i) x‖ = _
  rw [pairing_real_smul_left, pairing_sum_left]
  simp_rw [hn]
  rw [← RCLike.ofReal_sum, norm_smul, Real.norm_eq_abs, RCLike.norm_ofReal,
    abs_of_nonneg (inv_nonneg.mpr (logarithmicWeight_nonneg T.count)),
    abs_of_nonneg (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))]

end ThesisCommon.GowersMaurey
