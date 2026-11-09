import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra

/-!
# Uncentred covariance of a body

The paper takes covariance about the prescribed origin, without subtracting a
barycentre. Here the covariance tensor is evaluated on continuous real linear
functionals. This gives the coordinate-free bilinear form on the dual. Its
change-of-variables law is the dual form of `C(TS) = T C(S) T*`.
No convexity or central symmetry is used.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Normalised second moment, without centring at the mean. -/
noncomputable def normalizedSecondMoment (μ : Measure E) (ℓ k : E →L[ℝ] ℝ) : ℝ :=
  (μ.real univ)⁻¹ * ∫ x, ℓ x * k x ∂μ

/-- The covariance tensor of a set, paired with two covectors. -/
noncomputable def bodySecondMoment (μ : Measure E) (S : Set E)
    (ℓ k : E →L[ℝ] ℝ) : ℝ := normalizedSecondMoment (μ.restrict S) ℓ k

omit [BorelSpace E] in
theorem bodySecondMoment_eq (μ : Measure E) (S : Set E) (ℓ k : E →L[ℝ] ℝ) :
    bodySecondMoment μ S ℓ k = (μ.real S)⁻¹ * ∫ x in S, ℓ x * k x ∂μ := by
  simp [bodySecondMoment, normalizedSecondMoment]

omit [BorelSpace E] in
/-- Rescaling a measure does not change its normalised second moment. -/
theorem normalizedSecondMoment_smul (μ : Measure E) (c : ℝ≥0∞)
    (hc : c ≠ 0) (hcfin : c ≠ ∞) (ℓ k : E →L[ℝ] ℝ) :
    normalizedSecondMoment (c • μ) ℓ k = normalizedSecondMoment μ ℓ k := by
  have hcr : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc, hcfin⟩
  simp only [normalizedSecondMoment, measureReal_def, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, integral_smul_measure, mul_inv_rev]
  field_simp

/-- Exact pushforward law for arbitrary measures. -/
theorem normalizedSecondMoment_map (μ : Measure E) (e : E ≃L[ℝ] F)
    (ℓ k : F →L[ℝ] ℝ) :
    normalizedSecondMoment (μ.map e) ℓ k =
      normalizedSecondMoment μ (ℓ.comp e.toContinuousLinearMap)
        (k.comp e.toContinuousLinearMap) := by
  have hmass : (μ.map e).real univ = μ.real univ := by
    simp [measureReal_def, Measure.map_apply e.continuous.measurable]
  unfold normalizedSecondMoment
  rw [hmass]
  congr 1
  exact integral_map_equiv e.toHomeomorph.toMeasurableEquiv (fun x ↦ ℓ x * k x)

/-- Pushforward law with restriction to the actual image set. -/
theorem bodySecondMoment_map (μ : Measure E) (e : E ≃L[ℝ] F) (S : Set E)
    (ℓ k : F →L[ℝ] ℝ) :
    bodySecondMoment (μ.map e) (e '' S) ℓ k =
      bodySecondMoment μ S (ℓ.comp e.toContinuousLinearMap)
        (k.comp e.toContinuousLinearMap) := by
  unfold bodySecondMoment
  have hres := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.restrict_map μ (e '' S)
  change (μ.map e).restrict (e '' S) = (μ.restrict (e ⁻¹' (e '' S))).map e at hres
  rw [e.injective.preimage_image] at hres
  rw [hres]
  exact normalizedSecondMoment_map _ e ℓ k

/-- The integrands defining the covariance form are integrable on compact bodies. -/
theorem integrableOn_covarianceProduct (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {S : Set E} (hS : IsCompact S) (ℓ k : E →L[ℝ] ℝ) :
    IntegrableOn (fun x ↦ ℓ x * k x) S μ :=
  (ℓ.continuous.mul k.continuous).continuousOn.integrableOn_compact hS

omit [BorelSpace E] in
theorem bodySecondMoment_symm (μ : Measure E) (S : Set E) (ℓ k : E →L[ℝ] ℝ) :
    bodySecondMoment μ S ℓ k = bodySecondMoment μ S k ℓ := by
  simp only [bodySecondMoment, normalizedSecondMoment, mul_comm]

theorem bodySecondMoment_add_left (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {S : Set E} (hS : IsCompact S) (ℓ₁ ℓ₂ k : E →L[ℝ] ℝ) :
    bodySecondMoment μ S (ℓ₁ + ℓ₂) k =
      bodySecondMoment μ S ℓ₁ k + bodySecondMoment μ S ℓ₂ k := by
  simp only [bodySecondMoment, normalizedSecondMoment, ContinuousLinearMap.add_apply, add_mul]
  rw [integral_add (integrableOn_covarianceProduct μ hS ℓ₁ k)
    (integrableOn_covarianceProduct μ hS ℓ₂ k), mul_add]

omit [BorelSpace E] in
theorem bodySecondMoment_smul_left (μ : Measure E) (S : Set E)
    (a : ℝ) (ℓ k : E →L[ℝ] ℝ) :
    bodySecondMoment μ S (a • ℓ) k = a * bodySecondMoment μ S ℓ k := by
  simp only [bodySecondMoment, normalizedSecondMoment, ContinuousLinearMap.smul_apply,
    smul_eq_mul, mul_assoc, integral_const_mul]
  ring

theorem bodySecondMoment_add_right (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {S : Set E} (hS : IsCompact S) (ℓ k₁ k₂ : E →L[ℝ] ℝ) :
    bodySecondMoment μ S ℓ (k₁ + k₂) =
      bodySecondMoment μ S ℓ k₁ + bodySecondMoment μ S ℓ k₂ := by
  rw [bodySecondMoment_symm μ S ℓ (k₁ + k₂), bodySecondMoment_add_left μ hS]
  rw [bodySecondMoment_symm μ S k₁ ℓ, bodySecondMoment_symm μ S k₂ ℓ]

omit [BorelSpace E] in
theorem bodySecondMoment_smul_right (μ : Measure E) (S : Set E)
    (a : ℝ) (ℓ k : E →L[ℝ] ℝ) :
    bodySecondMoment μ S ℓ (a • k) = a * bodySecondMoment μ S ℓ k := by
  rw [bodySecondMoment_symm μ S ℓ (a • k), bodySecondMoment_smul_left,
    bodySecondMoment_symm μ S k ℓ]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A nonzero real linear functional cannot vanish on a neighbourhood of zero.
This is made constructive at the level needed for positivity: there is a point
of the specified interior at which the functional is nonzero. -/
theorem exists_nonzero_covector_on_interior {S : Set E} (h0 : (0 : E) ∈ interior S)
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) : ∃ x ∈ interior S, ℓ x ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v : E, ℓ v ≠ 0 := by
    by_contra! h
    apply hℓ
    ext x
    exact h x
  have hv0 : v ≠ 0 := by intro hv0; simp [hv0] at hv
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hnvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds h0)
  let t : ℝ := (r / 2) / ‖v‖
  have ht : 0 < t := div_pos (by positivity) hnvp
  have hnorm : ‖t • v‖ = r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact div_mul_cancel₀ _ hnv
  refine ⟨t • v, hball ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_zero_right, hnorm] using (half_lt_self hr)
  · rw [map_smul, smul_eq_mul]
    exact mul_ne_zero (ne_of_gt ht) hv

/-- The uncentred covariance is positive definite as a form on covectors.
The origin is the prescribed origin. No barycentre, convexity, or symmetry
assumption occurs in the proof. -/
theorem bodySecondMoment_pos (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] {S : Set E} (hS : IsCompact S)
    (h0 : (0 : E) ∈ interior S) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    0 < bodySecondMoment μ S ℓ ℓ := by
  obtain ⟨x, hx, hℓx⟩ := exists_nonzero_covector_on_interior h0 hℓ
  have hopen : IsOpen (interior S ∩ Function.support ℓ) :=
    isOpen_interior.inter ℓ.continuous.isOpen_support
  have hnonempty : (interior S ∩ Function.support ℓ).Nonempty := ⟨x, hx, hℓx⟩
  have hsupport : 0 < μ (Function.support (fun z ↦ ℓ z * ℓ z) ∩ S) := by
    apply (hopen.measure_pos μ hnonempty).trans_le
    apply measure_mono
    intro z hz
    exact ⟨mul_ne_zero hz.2 hz.2, interior_subset hz.1⟩
  have hint : 0 < ∫ z in S, ℓ z * ℓ z ∂μ := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (fun z ↦ mul_self_nonneg (ℓ z)))
      (integrableOn_covarianceProduct μ hS ℓ ℓ)).mpr
    exact hsupport
  have hmass : 0 < μ.real S :=
    ENNReal.toReal_pos (ne_of_gt (Measure.measure_pos_of_mem_nhds μ
      (mem_interior_iff_mem_nhds.mp h0))) hS.measure_ne_top
  rw [bodySecondMoment_eq]
  exact mul_pos (inv_pos.mpr hmass) hint

/-- The covariance transport formula for Lebesgue/Haar measure, evaluated on
covectors. The determinant factor in change of variables cancels against the
normalising volume. It is proved here rather than assumed as a covariance law. -/
theorem bodySecondMoment_image [FiniteDimensional ℝ E] (μ : Measure E)
    [Measure.IsAddHaarMeasure μ] (e : E ≃L[ℝ] E) (S : Set E) (ℓ k : E →L[ℝ] ℝ) :
    bodySecondMoment μ (e '' S) ℓ k =
      bodySecondMoment μ S (ℓ.comp e.toContinuousLinearMap)
        (k.comp e.toContinuousLinearMap) := by
  have hd : LinearMap.det e.toLinearEquiv.toLinearMap ≠ 0 :=
    e.toLinearEquiv.isUnit_det'.ne_zero
  let c : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.toLinearMap)⁻¹|
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hd))).ne'
  have hcf : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hmap : μ.map e = c • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd
  have hrescale : bodySecondMoment (μ.map e) (e '' S) ℓ k =
      bodySecondMoment μ (e '' S) ℓ k := by
    rw [hmap]
    unfold bodySecondMoment
    rw [Measure.restrict_smul]
    exact normalizedSecondMoment_smul _ c hc hcf ℓ k
  exact hrescale.symm.trans (bodySecondMoment_map μ e S ℓ k)

/-- The same tensor packaged as an actual symmetric bilinear form on the dual. -/
noncomputable def bodyCovarianceBilinForm (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) : LinearMap.BilinForm ℝ (E →L[ℝ] ℝ) :=
  LinearMap.mk₂ ℝ (bodySecondMoment μ S)
    (bodySecondMoment_add_left μ hS)
    (fun a ℓ k ↦ by simpa only [smul_eq_mul] using bodySecondMoment_smul_left μ S a ℓ k)
    (bodySecondMoment_add_right μ hS)
    (fun a ℓ k ↦ by simpa only [smul_eq_mul] using bodySecondMoment_smul_right μ S a ℓ k)

@[simp]
theorem bodyCovarianceBilinForm_apply (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) (ℓ k : E →L[ℝ] ℝ) :
    bodyCovarianceBilinForm μ S hS ℓ k = bodySecondMoment μ S ℓ k := rfl

/-- A positive-definite real symmetric bilinear form has an orthonormal basis.
This algebraic construction rescales an orthogonal basis. It avoids introducing
an auxiliary norm on the underlying vector space. -/
theorem exists_orthonormalBasis_bilinForm
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  have hdiag (i) : 0 < B (b i) (b i) := hpos _ (b.ne_zero i)
  let w : Fin (Module.finrank ℝ V) → ℝˣ := fun i ↦
    Units.mk0 (Real.sqrt (B (b i) (b i)))⁻¹
      (inv_ne_zero (Real.sqrt_pos.mpr (hdiag i)).ne')
  refine ⟨b.unitsSMul w, ?_⟩
  intro i j
  simp only [Module.Basis.unitsSMul_apply]
  change B ((w i : ℝ) • b i) ((w j : ℝ) • b j) = _
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    dsimp only [w]
    change (Real.sqrt (B (b i) (b i)))⁻¹ *
      ((Real.sqrt (B (b i) (b i)))⁻¹ * B (b i) (b i)) = 1
    calc
      _ = (Real.sqrt (B (b i) (b i)) * Real.sqrt (B (b i) (b i)))⁻¹ * B (b i) (b i) := by
        rw [mul_inv_rev]
        ring
      _ = (B (b i) (b i))⁻¹ * B (b i) (b i) := by
        rw [← pow_two, Real.sq_sqrt (hdiag i).le]
      _ = 1 := inv_mul_cancel₀ (hdiag i).ne'
  · rw [if_neg hij, hb hij, mul_zero, mul_zero]

/-- Covariance-orthonormal covectors exist for every compact body containing a
neighbourhood of the prescribed origin. They are the whitening coordinates. -/
theorem exists_covarianceOrthonormalBasis [FiniteDimensional ℝ E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {S : Set E} (hS : IsCompact S) (h0 : (0 : E) ∈ interior S) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ (E →L[ℝ] ℝ))) ℝ (E →L[ℝ] ℝ),
      ∀ i j, bodySecondMoment μ S (b i) (b j) = if i = j then 1 else 0 := by
  apply exists_orthonormalBasis_bilinForm (bodyCovarianceBilinForm μ S hS)
  · exact ⟨bodySecondMoment_symm μ S⟩
  · intro ℓ hℓ
    exact bodySecondMoment_pos μ hS h0 hℓ

section InnerOperator

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [CompleteSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The tensor `z ⊗ z`, as a rank-one real operator. -/
noncomputable def rankOneCovariance (z : G) : G →L[ℝ] G := (innerSL ℝ z).smulRight z

omit [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_rankOneCovariance : Continuous (rankOneCovariance : G → G →L[ℝ] G) :=
  Continuous.clm_apply
    ((ContinuousLinearMap.smulRightL ℝ G G).continuous.comp (innerSL ℝ).continuous) continuous_id

/-- The paper's covariance operator, taken about zero and normalised by volume. -/
noncomputable def covarianceOperator (μ : Measure G) (S : Set G) : G →L[ℝ] G :=
  (μ.real S)⁻¹ • ∫ z in S, rankOneCovariance z ∂μ

/-- Pairing the integrated operator with two vectors recovers the covariance
tensor. This also certifies agreement with the paper's operator convention. -/
theorem covarianceOperator_inner (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {S : Set G} (hS : IsCompact S) (x y : G) :
    inner ℝ (covarianceOperator μ S x) y =
      bodySecondMoment μ S (innerSL ℝ x) (innerSL ℝ y) := by
  have hint : IntegrableOn (rankOneCovariance : G → G →L[ℝ] G) S μ :=
    continuous_rankOneCovariance.continuousOn.integrableOn_compact hS
  let L : (G →L[ℝ] G) →L[ℝ] ℝ :=
    (innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ G x)
  have h := L.integral_comp_comm hint
  rw [bodySecondMoment_eq]
  simp only [covarianceOperator, ContinuousLinearMap.smul_apply, real_inner_smul_left]
  congr 1
  simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_coe, rankOneCovariance, ContinuousLinearMap.smulRight_apply,
    real_inner_smul_right, real_inner_comm, mul_comm] using h.symm

theorem covarianceOperator_inner_symm (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {S : Set G} (hS : IsCompact S) (x y : G) :
    inner ℝ (covarianceOperator μ S x) y = inner ℝ x (covarianceOperator μ S y) := by
  calc
    inner ℝ (covarianceOperator μ S x) y =
        bodySecondMoment μ S (innerSL ℝ x) (innerSL ℝ y) := covarianceOperator_inner μ hS x y
    _ = bodySecondMoment μ S (innerSL ℝ y) (innerSL ℝ x) := bodySecondMoment_symm μ S _ _
    _ = inner ℝ (covarianceOperator μ S y) x := (covarianceOperator_inner μ hS y x).symm
    _ = inner ℝ x (covarianceOperator μ S y) := real_inner_comm _ _

theorem covarianceOperator_pos (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] {S : Set G} (hS : IsCompact S)
    (h0 : (0 : G) ∈ interior S) {x : G} (hx : x ≠ 0) :
    0 < inner ℝ (covarianceOperator μ S x) x := by
  rw [covarianceOperator_inner μ hS]
  apply bodySecondMoment_pos μ hS h0
  intro hz
  have hz' : innerSL ℝ x = innerSL ℝ (0 : G) := by simpa using hz
  exact hx (innerSL_inj.mp hz')

theorem covarianceOperator_injective (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] {S : Set G} (hS : IsCompact S)
    (h0 : (0 : G) ∈ interior S) : Function.Injective (covarianceOperator μ S) := by
  intro x y hxy
  by_contra hne
  have hpos := covarianceOperator_pos μ hS h0 (sub_ne_zero.mpr hne)
  have hzero : covarianceOperator μ S (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [hzero, inner_zero_left] at hpos
  exact (lt_irrefl 0) hpos

omit [MeasurableSpace G] [BorelSpace G] in
/-- Pulling a real inner-product covector back is applying the adjoint to its
representing vector. -/
theorem innerSL_comp_eq_adjoint (A : G →L[ℝ] G) (x : G) :
    (innerSL ℝ x).comp A = innerSL ℝ (A.adjoint x) := by
  ext z
  exact (ContinuousLinearMap.adjoint_inner_left A z x).symm

/-- The exact operator-valued covariance change-of-variables formula (3) of
the paper. No central symmetry or convexity is used. -/
theorem covarianceOperator_image [FiniteDimensional ℝ G] (μ : Measure G)
    [Measure.IsAddHaarMeasure μ] {S : Set G} (hS : IsCompact S) (e : G ≃L[ℝ] G) :
    covarianceOperator μ (e '' S) =
      e.toContinuousLinearMap.comp
        ((covarianceOperator μ S).comp e.toContinuousLinearMap.adjoint) := by
  ext x
  apply ext_inner_right ℝ
  intro y
  calc
    inner ℝ (covarianceOperator μ (e '' S) x) y =
        bodySecondMoment μ (e '' S) (innerSL ℝ x) (innerSL ℝ y) :=
      covarianceOperator_inner μ (hS.image e.continuous) x y
    _ = bodySecondMoment μ S ((innerSL ℝ x).comp e.toContinuousLinearMap)
        ((innerSL ℝ y).comp e.toContinuousLinearMap) :=
      bodySecondMoment_image μ e S _ _
    _ = bodySecondMoment μ S (innerSL ℝ (e.toContinuousLinearMap.adjoint x))
        (innerSL ℝ (e.toContinuousLinearMap.adjoint y)) := by
      rw [innerSL_comp_eq_adjoint, innerSL_comp_eq_adjoint]
    _ = inner ℝ (covarianceOperator μ S (e.toContinuousLinearMap.adjoint x))
        (e.toContinuousLinearMap.adjoint y) :=
      (covarianceOperator_inner μ hS _ _).symm
    _ = inner ℝ (e (covarianceOperator μ S (e.toContinuousLinearMap.adjoint x))) y :=
      ContinuousLinearMap.adjoint_inner_right e.toContinuousLinearMap _ y
    _ = inner ℝ (e.toContinuousLinearMap.comp
        ((covarianceOperator μ S).comp e.toContinuousLinearMap.adjoint) x) y := rfl

/-- A body in covariance position has only orthogonal linear automorphisms.
This is the geometric implication used in Lemma 2.1(i). -/
theorem covariancePosition_inner_map [FiniteDimensional ℝ G] (μ : Measure G)
    [Measure.IsAddHaarMeasure μ] {S : Set G} (hS : IsCompact S)
    (hC : covarianceOperator μ S = ContinuousLinearMap.id ℝ G)
    (e : G ≃L[ℝ] G) (he : e '' S = S) (x y : G) :
    inner ℝ (e x) (e y) = inner ℝ x y := by
  have htransport := covarianceOperator_image μ hS e
  rw [he, hC] at htransport
  have hright : e.toContinuousLinearMap.comp e.toContinuousLinearMap.adjoint =
      ContinuousLinearMap.id ℝ G := by
    simpa only [ContinuousLinearMap.id_comp] using htransport.symm
  have hadj : ∀ z, e.toContinuousLinearMap.adjoint z = e.symm z := by
    intro z
    apply e.injective
    rw [e.apply_symm_apply]
    exact congrArg (fun A : G →L[ℝ] G ↦ A z) hright
  calc
    inner ℝ (e x) (e y) = inner ℝ x (e.toContinuousLinearMap.adjoint (e y)) :=
      (ContinuousLinearMap.adjoint_inner_right e.toContinuousLinearMap x (e y)).symm
    _ = inner ℝ x y := by rw [hadj, e.symm_apply_apply]

/-- The same conclusion as a bundled linear isometric equivalence, preserving
the original Euclidean norm and the specified body automorphism. -/
noncomputable def covariancePositionIsometry [FiniteDimensional ℝ G] (μ : Measure G)
    [Measure.IsAddHaarMeasure μ] {S : Set G} (hS : IsCompact S)
    (hC : covarianceOperator μ S = ContinuousLinearMap.id ℝ G)
    (e : G ≃L[ℝ] G) (he : e '' S = S) : G ≃ₗᵢ[ℝ] G :=
  e.toLinearEquiv.isometryOfInner (covariancePosition_inner_map μ hS hC e he)

@[simp]
theorem covariancePositionIsometry_apply [FiniteDimensional ℝ G] (μ : Measure G)
    [Measure.IsAddHaarMeasure μ] {S : Set G} (hS : IsCompact S)
    (hC : covarianceOperator μ S = ContinuousLinearMap.id ℝ G)
    (e : G ≃L[ℝ] G) (he : e '' S = S) (x : G) :
    covariancePositionIsometry μ hS hC e he x = e x := rfl

/-- Every compact real body containing a neighbourhood of zero can be put in
covariance position by a real-linear equivalence. The construction chooses
covariance-orthonormal covectors, then uses their evaluation coordinates.
This is an alternative to the matrix inverse-square-root construction in the
paper; no convexity or central symmetry is required. -/
theorem exists_covariancePosition [FiniteDimensional ℝ G] (μ : Measure G)
    [Measure.IsAddHaarMeasure μ] {S : Set G} (hS : IsCompact S)
    (h0 : (0 : G) ∈ interior S) :
    ∃ e : G ≃L[ℝ] G,
      covarianceOperator μ (e '' S) = ContinuousLinearMap.id ℝ G := by
  classical
  let ι := Fin (Module.finrank ℝ (G →L[ℝ] ℝ))
  obtain ⟨b, hb⟩ := exists_covarianceOrthonormalBasis μ hS h0
  let Φ : G →ₗ[ℝ] (ι → ℝ) := LinearMap.pi (fun i ↦ (b i).toLinearMap)
  have hinj : Function.Injective Φ := by
    intro x y hxy
    have heval : (ContinuousLinearMap.apply ℝ ℝ x).toLinearMap =
        (ContinuousLinearMap.apply ℝ ℝ y).toLinearMap := by
      apply b.ext
      intro i
      exact congrFun hxy i
    apply ext_inner_left ℝ
    intro v
    exact congrArg (fun L : (G →L[ℝ] ℝ) →ₗ[ℝ] ℝ ↦ L (innerSL ℝ v)) heval
  have hdim : Module.finrank ℝ G = Module.finrank ℝ (G →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ G).toLinearEquiv.finrank_eq
  have hdim' : Module.finrank ℝ G = Module.finrank ℝ (ι → ℝ) := by
    simpa only [ι, Module.finrank_pi_fintype, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hdim
  let ecoords : G ≃ₗ[ℝ] (ι → ℝ) := LinearEquiv.ofBijective Φ
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hinj⟩
  let b0 : OrthonormalBasis ι ℝ G :=
    (stdOrthonormalBasis ℝ G).reindex (finCongr hdim)
  let e0 : G ≃ₗ[ℝ] G := ecoords.trans b0.toBasis.equivFun.symm
  let e : G ≃L[ℝ] G := e0.toContinuousLinearEquiv
  have hcoord (i : ι) : (innerSL ℝ (b0 i)).comp e.toContinuousLinearMap = b i := by
    ext x
    change inner ℝ (b0 i) (e x) = b i x
    calc
      inner ℝ (b0 i) (e x) = b0.repr (e x) i := (b0.repr_apply_apply _ _).symm
      _ = ecoords x i := by
        change (b0.toBasis.equivFun (b0.toBasis.equivFun.symm (ecoords x))) i = _
        exact congrFun (b0.toBasis.equivFun.apply_symm_apply (ecoords x)) i
      _ = b i x := rfl
  refine ⟨e, ?_⟩
  have hlin : (covarianceOperator μ (e '' S)).toLinearMap =
      (ContinuousLinearMap.id ℝ G).toLinearMap := by
    apply b0.toBasis.ext
    intro j
    change covarianceOperator μ (e '' S) (b0 j) = b0 j
    apply b0.repr.injective
    ext i
    simp only [b0.repr_apply_apply]
    calc
      inner ℝ (b0 i) (covarianceOperator μ (e '' S) (b0 j)) =
          inner ℝ (covarianceOperator μ (e '' S) (b0 j)) (b0 i) := real_inner_comm _ _
      _ = bodySecondMoment μ (e '' S) (innerSL ℝ (b0 j)) (innerSL ℝ (b0 i)) :=
        covarianceOperator_inner μ (hS.image e.continuous) _ _
      _ = bodySecondMoment μ S ((innerSL ℝ (b0 j)).comp e.toContinuousLinearMap)
          ((innerSL ℝ (b0 i)).comp e.toContinuousLinearMap) := bodySecondMoment_image μ e S _ _
      _ = bodySecondMoment μ S (b j) (b i) := by rw [hcoord, hcoord]
      _ = if j = i then 1 else 0 := hb j i
      _ = inner ℝ (b0 i) (b0 j) := by rw [b0.inner_eq_ite]; simp only [eq_comm]
  ext x
  exact congrArg (fun L : G →ₗ[ℝ] G ↦ L x) hlin

end InnerOperator

end BanachIsometric
