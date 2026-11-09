import BanachIsometric.CanonicalMomentReferenceMap
import BanachIsometric.CanonicalHemisphereLipschitz
import BanachIsometric.GaugeLevelGeometry
import BanachIsometric.RadialHomeomorphismLipschitz
import BanachIsometric.SignedSimplexChainMoments
import BanachIsometric.LipschitzConeSupport

/-! The actual count of a radial reference cycle is supported by the literal
closed gauge sublevel. The interior count one gives a strictly positive
signed moment in each even weight. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set MeasureTheory
open scoped NNReal Topology

theorem rawSignedSimplexCount_cone_pushforward_zero_outside {X : Type*} [PseudoMetricSpace X]
    (n : ℕ) {p : (Fin (n + 1) → ℝ) → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    (f : C(X, Fin (n + 1) → ℝ)) {L : ℝ≥0} (hL : LipschitzWith L f) (hf : ∀ x, p (f x) = 1)
    (c : RawRationalChains X n) (hc : c ∈ rawLipschitzCarrier X n) {y : Fin (n + 1) → ℝ}
    (hy : 1 < p y) : rawSignedSimplexCount (n + 1) (rawLipschitzCone n (rawChainMap f n c)) y = 0 := by
  let F := (LinearMap.proj (R := ℚ) y).comp
    ((rawSignedSimplexCount (n + 1)).comp ((rawLipschitzCone n).comp (rawChainMap f n)))
  have hs : rawLipschitzCarrier X n ≤ LinearMap.ker F := by
    rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, ⟨K, hK⟩, rfl⟩
    change F (Finsupp.single σ 1) = 0
    have hmap : rawChainMap f n (Finsupp.single σ 1) = Finsupp.single (f.comp σ) 1 := by
      simp [rawChainMap]
    change rawSignedSimplexCount (n + 1) (rawLipschitzCone n (rawChainMap f n (Finsupp.single σ 1))) y = 0
    rw [hmap, rawLipschitzCone_single, rawSignedSimplexCount_single, one_smul]
    let τ := f.comp σ
    have hτ : ∃ M : ℝ≥0, LipschitzWith M τ := ⟨L * K, hL.comp hK⟩
    apply signedSimplexCount_eq_zero_off_range _ _ (exists_lipschitz_lipschitzSingularCone n τ hτ)
    rintro ⟨w, hw⟩
    change lipschitzSingularCone n τ w = y at hw
    rw [lipschitzSingularCone_apply n τ hτ, singularConeFun] at hw
    have hsub : p y ≤ 1 := by
      by_cases h : 0 < simplexConeRadius n w
      · rw [dif_pos h] at hw
        rw [← hw, hp.smul_nonneg _ h.le]
        change simplexConeRadius n w * p (f (σ (simplexConeBase n w h))) ≤ 1
        rw [hf, mul_one]
        exact simplexConeRadius_le_one n w
      · rw [dif_neg h] at hw
        rw [← hw, (hp.eq_zero_iff 0).mpr rfl]
        norm_num
    exact (not_lt_of_ge hsub) hy
  exact LinearMap.mem_ker.mp (hs hc)

end BanachIsometric.SingularPrism

namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory SingularPrism
open scoped NNReal Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem canonicalMoment_pos_of_interior_count {p : F → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hCount : let e := canonicalHemisphereChartCoordinates v n hdim
      let a := (canonicalSuspensionCycle v n hdim).val
      let c := rawLipschitzCone (n + 2)
        (rawChainMap (canonicalMomentReferenceMap hp hcont v n hdim) (n + 2) a)
      ∀ᵐ z ∂(volume : Measure (Fin (n + 3) → ℝ)), 0 < p (e.symm z) → p (e.symm z) < 1 →
        rawSignedSimplexCount (n + 3) c z = 1) (k : ℕ) :
    0 < rawSignedSimplexMoment (n + 3) volume
      (fun z => ‖(canonicalHemisphereChartCoordinates v n hdim).symm z‖ ^ (2 * k))
      (rawLipschitzCone (n + 2) (rawChainMap (canonicalMomentReferenceMap hp hcont v n hdim)
        (n + 2) (canonicalSuspensionCycle v n hdim).val)) := by
  letI : Nontrivial F := ⟨⟨v.val, 0, ne_zero_of_mem_unit_sphere v⟩⟩
  letI : MeasurableSpace F := borel F
  letI : BorelSpace F := ⟨rfl⟩
  let e := canonicalHemisphereChartCoordinates v n hdim
  let a := (canonicalSuspensionCycle v n hdim).val
  let f := canonicalMomentReferenceMap hp hcont v n hdim
  let c := rawLipschitzCone (n + 2) (rawChainMap f (n + 2) a)
  let μ : Measure (Fin (n + 3) → ℝ) := volume
  let q := p ∘ e.symm
  let g := fun z => ‖e.symm z‖ ^ (2 * k)
  have hgc : Continuous g := e.symm.continuous.norm.pow _
  have hq : IsDefinitePositiveHomogeneous q := by
    refine ⟨fun z => hp.nonneg (e.symm z),
      fun z => (hp.eq_zero_iff (e.symm z)).trans e.symm.map_eq_zero_iff, ?_⟩
    intro t ht z
    change p (e.symm (t • z)) = t * p (e.symm z)
    rw [e.symm.map_smul, hp.smul_nonneg _ ht]
  have hqc : Continuous q := hcont.comp e.symm.continuous
  obtain ⟨L, hL⟩ := exists_lipschitz_radialGaugeMap hp hSphere
  have hf : LipschitzWith _ f := e.lipschitz.comp (hL.comp (LipschitzWith.subtype_val _))
  have hfa (x : sphere (0 : F) 1) : q (f x) = 1 := by
    change p (e.symm (e (radialGaugeMap p x.val))) = 1
    rw [e.symm_apply_apply, gauge_radialGaugeMap hp, norm_eq_of_mem_sphere x]
  have ha : a ∈ rawLipschitzCarrier _ (n + 2) := canonicalSuspensionCycle_mem_lipschitz v n hdim
  have hc : c ∈ rawLipschitzCarrier _ (n + 3) := rawLipschitzCone_preserves_lipschitz _
    (rawChainMap_preserves_lipschitz f hf _ ha)
  let B : Set (Fin (n + 3) → ℝ) := {z | q z ≤ 1}
  have hB : MeasurableSet B := (isClosed_le hqc continuous_const).measurableSet
  have hnull : μ {z | q z = 1} = 0 := by
    rw [← hq.frontier_pos_sublevel_eq_level hqc zero_lt_one]
    exact measure_frontier_pos_sublevel_eq_zero μ hq hqc zero_lt_one
  have hOffOne : ∀ᵐ z ∂μ, q z ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  have hOffZero : ∀ᵐ z ∂μ, q z ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, hq.eq_zero_iff]
    exact measure_singleton (0 : Fin (n + 3) → ℝ)
  have hcount : ∀ᵐ z ∂μ, rawSignedSimplexCount (n + 3) c z = B.indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [hCount, hOffOne, hOffZero] with z hz hOne hZero
    by_cases h : z ∈ B
    · rw [indicator_of_mem h]
      exact hz (lt_of_le_of_ne (hq.nonneg z) (Ne.symm hZero)) (lt_of_le_of_ne h hOne)
    · rw [indicator_of_notMem h]
      exact rawSignedSimplexCount_cone_pushforward_zero_outside (n + 2) hq f hf hfa a ha (lt_of_not_ge h)
  have hval : rawSignedSimplexMoment (n + 3) μ g c = ∫ z in B, g z ∂μ := by
    rw [rawSignedSimplexMoment_eq_integral _ μ c hc hgc, ← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards [hcount] with z hz
    rw [hz]
    by_cases h : z ∈ B <;> simp [h]
  let ν : Measure F := Measure.map e.symm μ
  letI : ν.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
  have htrans := setIntegral_map_equiv (μ := μ) e.symm.toHomeomorph.toMeasurableEquiv
    (fun x : F => ‖x‖ ^ (2 * k)) {x | p x ≤ 1}
  change rawSignedSimplexMoment (n + 3) μ g c > 0
  rw [hval, ← show (∫ x in {x : F | p x ≤ 1}, ‖x‖ ^ (2 * k) ∂ν) = ∫ z in B, g z ∂μ from htrans]
  exact integral_norm_pow_unit_sublevel_pos ν hp hcont (2 * k)

end BanachIsometric.ExactSectionPrincipalData
