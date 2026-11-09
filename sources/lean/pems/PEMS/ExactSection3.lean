import PEMS.OrderInfrastructure
import PEMS.LatticeIsomorphisms
import PEMS.KernelInfrastructure
import PEMS.SeparableL1Projection
import PEMS.LocalizedMeasureNormalization
import ThesisCommon.Analysis.L1SequenceFiniteEnvelope
import ThesisCommon.Analysis.LebesgueLpRestrictionAlgebra

/-! The natural complemented sublattices in Proposition 3.9 and the
unit-mass formulation of Proposition 3.10. In the support argument, only
genuine sigma-finite supports of integrable functions are used. -/

noncomputable section
open MeasureTheory MeasurableSpace Set Filter TopologicalSpace ThesisCommon
open scoped ENNReal

namespace PEMS

variable {X : Type*} [mX : MeasurableSpace X] (μ : Measure X)

/-- The finite case of Proposition 3.9 with its actual contractive projection
and the canonical inclusion of the trimmed L¹ as a sublattice. -/
theorem proposition_3_9_finite [IsFiniteMeasure μ]
    (M : Set (Lp ℝ 1 μ)) (hM : IsSeparable M) :
    ∃ (m : MeasurableSpace X) (hm : m ≤ mX), @CountablyGenerated X m ∧
      M ⊆ range (lOneSubsigmaEmbedding μ hm) ∧
      (∀ u v, lOneSubsigmaEmbedding μ hm (u ⊔ v) =
        lOneSubsigmaEmbedding μ hm u ⊔ lOneSubsigmaEmbedding μ hm v) ∧
      ∃ Q : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ,
        range Q = range (lOneSubsigmaEmbedding μ hm) ∧ Q.comp Q = Q ∧ ‖Q‖ ≤ 1 := by
  obtain ⟨m, hm, Q, hmc, hMm, hrange, hproj, hnorm⟩ :=
    separable_L1_complemented_envelope μ M hM
  rw [← range_lOneSubsigmaEmbedding μ hm] at hMm hrange
  exact ⟨m, hm, hmc, hMm, lOneSubsigmaEmbedding_sup μ hm, Q, hrange, hproj, hnorm⟩

private def lOneMeasureEq {μ ν : Measure X} (h : μ = ν) : Lp ℝ 1 μ ≃ₗᵢ[ℝ] Lp ℝ 1 ν := by
  subst ν
  exact LinearIsometryEquiv.refl ℝ _

private theorem lOneMeasureEq_sup {μ ν : Measure X} (h : μ = ν) (f g : Lp ℝ 1 μ) :
    lOneMeasureEq h (f ⊔ g) = lOneMeasureEq h f ⊔ lOneMeasureEq h g := by
  subst ν
  rfl

/-- The measure on the measurable subtype and the restriction supported on
the ambient type give the same L¹ space via actual pullback. -/
private def traceLOneEquiv {Ω : Set X} (hΩ : MeasurableSet Ω) :
    Lp ℝ 1 (μ.restrict Ω) ≃ₗᵢ[ℝ] Lp ℝ 1 (μ.comap (Subtype.val : Ω → X)) :=
  (lOneMeasureEq (map_comap_subtype_coe hΩ μ).symm).trans
    (lpComapEquiv (μ.comap (Subtype.val : Ω → X)) Subtype.val measurable_subtype_coe rfl 1)

private theorem traceLOneEquiv_sup {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f g : Lp ℝ 1 (μ.restrict Ω)) :
    traceLOneEquiv μ hΩ (f ⊔ g) = traceLOneEquiv μ hΩ f ⊔ traceLOneEquiv μ hΩ g := by
  simp only [traceLOneEquiv, LinearIsometryEquiv.trans_apply, lOneMeasureEq_sup, lpComapEquiv_sup]

private theorem traceLOneEquiv_symm_sup {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f g : Lp ℝ 1 (μ.comap (Subtype.val : Ω → X))) :
    (traceLOneEquiv μ hΩ).symm (f ⊔ g) =
      (traceLOneEquiv μ hΩ).symm f ⊔ (traceLOneEquiv μ hΩ).symm g := by
  apply (traceLOneEquiv μ hΩ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, traceLOneEquiv_sup,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

private theorem extendLOne_sup {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f g : Lp ℝ 1 (μ.restrict Ω)) :
    lebesgueLpExtend (𝕜 := ℝ) Ω hΩ (f ⊔ g) =
      lebesgueLpExtend (𝕜 := ℝ) Ω hΩ f ⊔ lebesgueLpExtend (𝕜 := ℝ) Ω hΩ g := by
  apply Lp.ext
  filter_upwards [lebesgueLpExtend_coe (𝕜 := ℝ) Ω hΩ (f ⊔ g),
    lebesgueLpExtend_coe (𝕜 := ℝ) Ω hΩ f, lebesgueLpExtend_coe (𝕜 := ℝ) Ω hΩ g,
    (ae_restrict_iff' hΩ).mp (Lp.coeFn_sup f g),
    Lp.coeFn_sup (lebesgueLpExtend (𝕜 := ℝ) Ω hΩ f) (lebesgueLpExtend (𝕜 := ℝ) Ω hΩ g)]
    with x hfg hf hg hsup hout
  change _ = _ at hfg hf hg
  rw [hfg, hout, Pi.sup_apply, hf, hg]
  by_cases hx : x ∈ Ω
  · simpa only [indicator_of_mem hx, Pi.sup_apply] using hsup hx
  · simp [indicator_of_notMem hx]

private abbrev traceMeasureOn {Ω : Set X} :
    @Measure Ω (mX.comap (Subtype.val : Ω → X)) :=
  @Measure.comap Ω X (mX.comap (Subtype.val : Ω → X)) mX (Subtype.val : Ω → X) μ

/-- Include `L¹(Ω, Σ̂, μ)` in the original `L¹`, using restriction of the
trace measure to `Σ̂` and extension by zero outside `Ω`. -/
def exactSection3TraceEmbedding {Ω : Set X} (hΩ : MeasurableSet Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mX.comap (Subtype.val : Ω → X)) :
    Lp ℝ 1 ((traceMeasureOn μ (Ω := Ω)).trim hm) →ₗᵢ[ℝ] Lp ℝ 1 μ where
  toFun := fun u => lebesgueLpExtend (𝕜 := ℝ) (μ := μ) Ω hΩ
    ((traceLOneEquiv μ hΩ).symm (lOneSubsigmaEmbedding (traceMeasureOn μ (Ω := Ω)) hm u))
  map_add' u v := by simp only [map_add]
  map_smul' c u := by simp only [map_smul, RingHom.id_apply]
  norm_map' u :=
    ((lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := μ) Ω hΩ).norm_map _).trans
      (((traceLOneEquiv μ hΩ).symm.norm_map _).trans
        ((lOneSubsigmaEmbedding (traceMeasureOn μ (Ω := Ω)) hm).norm_map u))

theorem exactSection3TraceEmbedding_sup {Ω : Set X} (hΩ : MeasurableSet Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mX.comap (Subtype.val : Ω → X))
    (u v : Lp ℝ 1 ((traceMeasureOn μ (Ω := Ω)).trim hm)) :
    exactSection3TraceEmbedding μ hΩ hm (u ⊔ v) =
      exactSection3TraceEmbedding μ hΩ hm u ⊔ exactSection3TraceEmbedding μ hΩ hm v := by
  change lebesgueLpExtend (𝕜 := ℝ) (μ := μ) Ω hΩ
      ((traceLOneEquiv μ hΩ).symm (lOneSubsigmaEmbedding (traceMeasureOn μ (Ω := Ω)) hm (u ⊔ v))) =
    lebesgueLpExtend (𝕜 := ℝ) (μ := μ) Ω hΩ
      ((traceLOneEquiv μ hΩ).symm (lOneSubsigmaEmbedding (traceMeasureOn μ (Ω := Ω)) hm u)) ⊔
    lebesgueLpExtend (𝕜 := ℝ) (μ := μ) Ω hΩ
      ((traceLOneEquiv μ hΩ).symm (lOneSubsigmaEmbedding (traceMeasureOn μ (Ω := Ω)) hm v))
  rw [lOneSubsigmaEmbedding_sup, traceLOneEquiv_symm_sup, extendLOne_sup]

private theorem sigmaFinite_trace {Ω : Set X} (hΩ : MeasurableSet Ω)
    [SigmaFinite (μ.restrict Ω)] : SigmaFinite (μ.comap (Subtype.val : Ω → X)) := by
  let ρ := μ.comap (Subtype.val : Ω → X)
  let C (n : ℕ) : Set Ω := Subtype.val ⁻¹' spanningSets (μ.restrict Ω) n
  apply Measure.sigmaFinite_of_countable (countable_range C)
  · rintro _ ⟨n, rfl⟩
    change ρ (Subtype.val ⁻¹' spanningSets (μ.restrict Ω) n) < ⊤
    rw [← Measure.map_apply measurable_subtype_coe (measurableSet_spanningSets _ _),
      map_comap_subtype_coe hΩ μ]
    exact measure_spanningSets_lt_top _ _
  · rw [sUnion_range]
    simp only [C, ← preimage_iUnion, iUnion_spanningSets, preimage_univ]

private theorem exists_sigmaFinite_trim_envelope [SigmaFinite μ]
    (M : Set (Lp ℝ 1 μ)) (hM : IsSeparable M) :
    ∃ (m : MeasurableSpace X) (hm : m ≤ mX), @CountablyGenerated X m ∧
      SigmaFinite (μ.trim hm) ∧ M ⊆ lOneSubsigma μ m := by
  let m₁ := MeasurableSpace.generateFrom (range (spanningSets μ))
  have hm₁ : m₁ ≤ mX := MeasurableSpace.generateFrom_le (by
    rintro _ ⟨n, rfl⟩
    exact measurableSet_spanningSets μ n)
  have hmc₁ : @CountablyGenerated X m₁ := ⟨_, countable_range _, rfl⟩
  obtain ⟨m, hm, hsub, hmc, hM⟩ :=
    exists_countablyGenerated_lOneSubsigma_enlargement μ m₁ hm₁ hmc₁ M hM
  refine ⟨m, hm, hmc, ?_, hM⟩
  apply Measure.sigmaFinite_of_countable (countable_range (spanningSets μ))
  · rintro _ ⟨n, rfl⟩
    have hset : MeasurableSet[m] (spanningSets μ n) :=
      hsub _ (measurableSet_generateFrom (mem_range_self n))
    rw [trim_measurableSet_eq hm hset]
    exact measure_spanningSets_lt_top _ _
  · rw [sUnion_range, iUnion_spanningSets]

/-- Proposition 3.9(2) with the printed strict-localizability hypothesis.
The construction in fact works for an arbitrary original measure: the
countable dense family has one measurable sigma-finite support. The finite
measure covering sets are retained in the smaller sigma-algebra so that
conditional expectation is an actual contractive projection. -/
theorem proposition_3_9_strictlyLocalizable (_hμ : StrictlyLocalizable μ)
    (M : Set (Lp ℝ 1 μ)) (hM : IsSeparable M) :
    ∃ (Ω : Set X) (hΩ : MeasurableSet Ω) (_ : SigmaFinite (μ.restrict Ω))
      (m : MeasurableSpace Ω) (hm : m ≤ mX.comap (Subtype.val : Ω → X)),
      @CountablyGenerated Ω m ∧ M ⊆ range (exactSection3TraceEmbedding μ hΩ hm) ∧
      (∀ u v, exactSection3TraceEmbedding μ hΩ hm (u ⊔ v) =
        exactSection3TraceEmbedding μ hΩ hm u ⊔ exactSection3TraceEmbedding μ hΩ hm v) ∧
      ∃ Q : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ,
        range Q = range (exactSection3TraceEmbedding μ hΩ hm) ∧ Q.comp Q = Q ∧ ‖Q‖ ≤ 1 := by
  have hDense := hM
  obtain ⟨D, hD, hMD⟩ := hDense
  obtain ⟨f, hf⟩ := countable_iff_exists_subset_range.mp hD
  obtain ⟨Ω, hΩ, hσ, hsupport⟩ := exists_sigmaFinite_lOne_sequence_support f
  letI := hσ
  let ρ := μ.comap (Subtype.val : Ω → X)
  letI : SigmaFinite ρ := sigmaFinite_trace μ hΩ
  let e := traceLOneEquiv μ hΩ
  let E := lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := μ) Ω hΩ
  let R := lebesgueLpRestrict (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := μ) Ω
  have hER (x : Lp ℝ 1 μ) (hx : x ∈ M) : E (R x) = x := by
    apply closure_minimal (t := {x | E (R x) = x}) ?_ (isClosed_eq
      (E.continuous.comp R.continuous) continuous_id) (hMD hx)
    intro y hy
    obtain ⟨n, rfl⟩ := hf hy
    exact lebesgueLpExtend_restrict_of_supported Ω hΩ (f n) (hsupport n)
  have hsep : IsSeparable ((e ∘ R) '' M) := hM.image (e.continuous.comp R.continuous)
  obtain ⟨m, hm, hmc, hsigma, hMm⟩ := exists_sigmaFinite_trim_envelope ρ _ hsep
  letI := hsigma
  let J₀ := lOneSubsigmaEmbedding ρ hm
  let J := exactSection3TraceEmbedding μ (Ω := Ω) hΩ (m := m) hm
  let C := condExpL1CLM ℝ hm ρ
  let U : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ρ := e.toLinearIsometry.toContinuousLinearMap.comp R
  let V : Lp ℝ 1 ρ →L[ℝ] Lp ℝ 1 μ := E.toContinuousLinearMap.comp
    e.symm.toLinearIsometry.toContinuousLinearMap
  let CU : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ρ := C.comp U
  let Q : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ := V.comp CU
  have hC_mem (g : Lp ℝ 1 ρ) : C g ∈ lOneSubsigma ρ m :=
    aestronglyMeasurable_condExpL1CLM g
  have hC_fix (g : Lp ℝ 1 ρ) (hg : g ∈ lOneSubsigma ρ m) : C g = g :=
    condExpL1CLM_of_aestronglyMeasurable' g hg
  have hJ₀ (v : Lp ℝ 1 (ρ.trim hm)) : J₀ v ∈ lOneSubsigma ρ m := by
    change J₀ v ∈ (lOneSubsigma ρ m : Set (Lp ℝ 1 ρ))
    rw [← range_lOneSubsigmaEmbedding ρ hm]
    exact mem_range_self v
  have hQ_fix (v : Lp ℝ 1 (ρ.trim hm)) : Q (J v) = J v := by
    change E (e.symm (C (e (R (E (e.symm (J₀ v))))))) = E (e.symm (J₀ v))
    rw [lebesgueLpRestrict_extend, LinearIsometryEquiv.apply_symm_apply, hC_fix _ (hJ₀ v)]
  have hrange : range Q = range J := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy := hC_mem (e (R y))
      change C (e (R y)) ∈ (lOneSubsigma ρ m : Set (Lp ℝ 1 ρ)) at hy
      rw [← range_lOneSubsigmaEmbedding ρ hm] at hy
      obtain ⟨v, hv⟩ := hy
      exact ⟨v, congrArg (fun z => E (e.symm z)) hv⟩
    · rintro ⟨v, rfl⟩
      exact ⟨J v, hQ_fix v⟩
  refine ⟨Ω, hΩ, hσ, m, hm, hmc, ?_, exactSection3TraceEmbedding_sup μ hΩ hm,
    Q, hrange, ?_, ?_⟩
  · intro x hx
    have hx' := hMm (mem_image_of_mem (e ∘ R) hx)
    rw [← range_lOneSubsigmaEmbedding ρ hm] at hx'
    obtain ⟨v, hv⟩ := hx'
    refine ⟨v, ?_⟩
    change E (e.symm (J₀ v)) = x
    rw [show J₀ v = e (R x) from hv, e.symm_apply_apply, hER x hx]
  · apply ContinuousLinearMap.ext
    intro x
    have hx := mem_range_self (f := Q) x
    rw [hrange] at hx
    obtain ⟨v, hv⟩ := hx
    change Q (Q x) = Q x
    rw [← hv, hQ_fix]
  · have hC : ‖C‖ ≤ 1 :=
      L1.norm_setToL1_le (dominatedFinMeasAdditive_condExpInd ℝ hm ρ) zero_le_one
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖E (e.symm (C (e (R x))))‖ ≤ 1 * ‖x‖
    rw [E.norm_map, e.symm.norm_map, one_mul]
    calc
      ‖C (e (R x))‖ ≤ ‖C‖ * ‖e (R x)‖ := C.le_opNorm _
      _ ≤ ‖R x‖ := by simpa only [e.norm_map, one_mul] using
          mul_le_mul_of_nonneg_right hC (norm_nonneg (R x))
      _ ≤ ‖x‖ := by
        calc
          ‖R x‖ ≤ ‖R‖ * ‖x‖ := R.le_opNorm _
          _ ≤ ‖x‖ := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (norm_lebesgueLpRestrict_le (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := μ) Ω)
              (norm_nonneg x)

/-- Proposition 3.10, with the printed positive-mass premise and the
unconditional conclusion that the new mass of the specified set is one. -/
theorem proposition_3_10 (hμ : StrictlyLocalizable μ)
    (s : Set X) (hs : MeasurableSet s) [SigmaFinite (μ.restrict s)] (hmass : μ s ≠ 0) :
    ∃ (ν : Measure X) (Ψ : Lp ℝ 1 μ ≃ₗᵢ[ℝ] Lp ℝ 1 ν)
      (H : Lp ℝ ∞ μ → Lp ℝ ∞ ν),
      StrictlyLocalizable ν ∧ ν s = 1 ∧
      (∀ f k, Ψ f ≤ Ψ k ↔ f ≤ k) ∧ (∀ h, H h =ᵐ[ν] h) ∧
      ∀ h f, Ψ (h • f : Lp ℝ 1 μ) = (H h • Ψ f : Lp ℝ 1 ν) := by
  obtain ⟨ν, Ψ, H, hν, _, _, hunit, horder, hH, hcomm⟩ :=
    localized_sigmaFinite_to_finite_lattice_isometry hμ s hs
  exact ⟨ν, Ψ, H, hν, hunit hmass, horder, hH, hcomm⟩

end PEMS
