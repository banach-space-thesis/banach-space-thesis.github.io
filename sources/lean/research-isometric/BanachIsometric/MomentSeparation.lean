import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic.FunProp

/-!
# Polynomial moments determine compactly supported measures

The separation argument in Lemma 2.1 of Acuaviva--Kania uses all polynomial
moments, including odd moments. No symmetry or convexity is required here.
Stone--Weierstrass supplies density; continuity of integration extends equality
from polynomial tests to all continuous tests and hence to the measures.
-/

noncomputable section

namespace BanachIsometric

open MeasureTheory
open scoped Topology ENNReal

section CompactIntegration

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Integration on continuous functions over a compact space, with the uniform
norm. This is bounded by the total mass, without a probability assumption. -/
def continuousIntegral (μ : Measure X) [IsFiniteMeasure μ] : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => by
        exact integral_add
          ((ContinuousMap.linearIsometryBoundedOfCompact X ℝ ℝ f).integrable μ)
          ((ContinuousMap.linearIsometryBoundedOfCompact X ℝ ℝ g).integrable μ)
      map_smul' := fun r f => by
        exact integral_smul r f }
    (μ.real Set.univ) (by
      intro f
      simpa using
        (ContinuousMap.linearIsometryBoundedOfCompact X ℝ ℝ f).norm_integral_le_mul_norm μ)

@[simp] theorem continuousIntegral_apply (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℝ)) : continuousIntegral μ f = ∫ x, f x ∂μ := rfl

/-- Equality on any point-separating real subalgebra determines finite Borel
measures on a compact space admitting continuous approximation of closed sets.
The density hypothesis is proved by Stone--Weierstrass, not assumed. -/
theorem measure_eq_of_subalgebra_integrals [HasOuterApproxClosed X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    (heq : ∀ f ∈ A, ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  have hclosed : IsClosed {f : C(X, ℝ) | continuousIntegral μ f = continuousIntegral ν f} :=
    isClosed_eq (continuousIntegral μ).continuous (continuousIntegral ν).continuous
  have hsubset : (A : Set C(X, ℝ)) ⊆
      {f : C(X, ℝ) | continuousIntegral μ f = continuousIntegral ν f} := by
    intro f hf
    exact heq f hf
  have hall (f : C(X, ℝ)) : ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
    apply closure_minimal hsubset hclosed
    exact ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints A hA f
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact hall f.toContinuousMap

end CompactIntegration

section PolynomialTests

variable {ι X : Type*} [TopologicalSpace X]

/-- Polynomial tests obtained from a family of real continuous coordinates. -/
def continuousPolynomialEvaluation (v : ι → C(X, ℝ)) :
    MvPolynomial ι ℝ →ₐ[ℝ] C(X, ℝ) := MvPolynomial.aeval v

@[simp] theorem continuousPolynomialEvaluation_apply (v : ι → C(X, ℝ))
    (P : MvPolynomial ι ℝ) (x : X) :
    continuousPolynomialEvaluation v P x = MvPolynomial.eval (fun i => v i x) P := by
  simpa [continuousPolynomialEvaluation, MvPolynomial.coe_aeval_eq_eval] using
    (MvPolynomial.comp_aeval_apply (f := v) (ContinuousMap.evalAlgHom ℝ ℝ x) P)

/-- Point-separating coordinates generate a point-separating polynomial algebra. -/
theorem continuousPolynomialEvaluation_separatesPoints (v : ι → C(X, ℝ))
    (hv : ∀ x y : X, x ≠ y → ∃ i, v i x ≠ v i y) :
    (continuousPolynomialEvaluation v).range.SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ := hv x y hxy
  refine ⟨fun z => v i z, ⟨v i, ?_, rfl⟩, hi⟩
  exact (continuousPolynomialEvaluation v).mem_range.mpr
    ⟨MvPolynomial.X i, MvPolynomial.aeval_X v i⟩

/-- All polynomial moments of separating coordinates determine a finite measure
on a compact space. The coordinates may be an infinite family. -/
theorem measure_eq_of_polynomial_coordinate_integrals [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [HasOuterApproxClosed X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (v : ι → C(X, ℝ)) (hv : ∀ x y : X, x ≠ y → ∃ i, v i x ≠ v i y)
    (heq : ∀ P : MvPolynomial ι ℝ,
      ∫ x, MvPolynomial.eval (fun i => v i x) P ∂μ =
        ∫ x, MvPolynomial.eval (fun i => v i x) P ∂ν) : μ = ν := by
  apply measure_eq_of_subalgebra_integrals (continuousPolynomialEvaluation v).range
    (continuousPolynomialEvaluation_separatesPoints v hv)
  intro f hf
  obtain ⟨P, rfl⟩ := (continuousPolynomialEvaluation v).mem_range.mp hf
  simpa using heq P

end PolynomialTests

/-- Concrete compact-coordinate form of the moment separation used in the
paper. The measures live on the compact set itself; no symmetry is assumed. -/
theorem measure_eq_of_compact_polynomial_integrals (n : ℕ)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    {μ ν : Measure K} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (heq : ∀ P : MvPolynomial (Fin n) ℝ,
      ∫ x : K, MvPolynomial.eval x.val P ∂μ =
        ∫ x : K, MvPolynomial.eval x.val P ∂ν) : μ = ν := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let v : Fin n → C(K, ℝ) := fun i =>
    ⟨fun x => x.val i, (continuous_apply i).comp continuous_subtype_val⟩
  apply measure_eq_of_polynomial_coordinate_integrals v
  · intro x y hxy
    by_contra! h
    apply hxy
    apply Subtype.ext
    funext i
    exact h i
  · exact heq

/-- Ambient form: two finite measures concentrated on a common compact set are
equal when all their polynomial moments agree. No centering or symmetry is
assumed for the compact set. -/
theorem measure_eq_of_supported_compact_polynomial_integrals (n : ℕ)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    {μ ν : Measure (Fin n → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ Kᶜ = 0) (hν : ν Kᶜ = 0)
    (heq : ∀ P : MvPolynomial (Fin n) ℝ,
      ∫ x, MvPolynomial.eval x P ∂μ = ∫ x, MvPolynomial.eval x P ∂ν) : μ = ν := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hμr : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hμ
  have hνr : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem hν
  have hc : μ.comap (Subtype.val : K → (Fin n → ℝ)) =
      ν.comap (Subtype.val : K → (Fin n → ℝ)) := by
    apply measure_eq_of_compact_polynomial_integrals n K hK
    intro P
    calc
      ∫ x : K, MvPolynomial.eval x.val P ∂μ.comap Subtype.val =
          ∫ x, MvPolynomial.eval x P ∂μ := by
        simpa only [hμr] using
          (integral_subtype_comap (μ := μ) hKm (fun x => MvPolynomial.eval x P))
      _ = ∫ x, MvPolynomial.eval x P ∂ν := heq P
      _ = ∫ x : K, MvPolynomial.eval x.val P ∂ν.comap Subtype.val := by
        simpa only [hνr] using
          (integral_subtype_comap (μ := ν) hKm (fun x => MvPolynomial.eval x P)).symm
  have hm := congrArg (Measure.map (Subtype.val : K → (Fin n → ℝ))) hc
  rwa [map_comap_subtype_coe hKm, map_comap_subtype_coe hKm, hμr, hνr] at hm

private theorem power_product_eq_ordered_product {ι : Type*} [Fintype ι]
    (d : ι → ℕ) :
    ∃ r : ℕ, ∃ indices : Fin r → ι,
      ∀ x : ι → ℝ, (∏ i, x i ^ d i) = ∏ j, x (indices j) := by
  classical
  let α := (i : ι) × Fin (d i)
  let e := Fintype.equivFin α
  refine ⟨Fintype.card α, fun j => (e.symm j).1, ?_⟩
  intro x
  calc
    (∏ i, x i ^ d i) = ∏ a : α, x a.1 := by simp [α, Fintype.prod_sigma]
    _ = ∏ j : Fin (Fintype.card α), x (e.symm j).1 :=
      Fintype.prod_equiv e _ _ (by intro a; simp)

/-- Ordered tensor moments of every order include all polynomial moments.
Order zero records the total mass; for probability measures this is automatic.
Odd orders are retained, as required for non-symmetric bodies in Lemma 2.1. -/
theorem measure_eq_of_compact_tensor_integrals (n : ℕ)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    {μ ν : Measure K} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (heq : ∀ (r : ℕ) (indices : Fin r → Fin n),
      ∫ x : K, (∏ j, x.val (indices j)) ∂μ =
        ∫ x : K, (∏ j, x.val (indices j)) ∂ν) : μ = ν := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hpowers (d : Fin n →₀ ℕ) :
      ∫ x : K, (∏ i, x.val i ^ d i) ∂μ =
        ∫ x : K, (∏ i, x.val i ^ d i) ∂ν := by
    obtain ⟨r, indices, hr⟩ := power_product_eq_ordered_product (fun i => d i)
    simpa only [← hr] using heq r indices
  apply measure_eq_of_compact_polynomial_integrals n K hK
  intro P
  have hint (ρ : Measure K) [IsFiniteMeasure ρ] (d : Fin n →₀ ℕ) :
      Integrable (fun x : K => P.coeff d * ∏ i, x.val i ^ d i) ρ := by
    let f : C(K, ℝ) := ⟨(fun x : K => P.coeff d * ∏ i, x.val i ^ d i),
      continuous_const.mul (continuous_finset_prod _ fun i _ =>
        ((continuous_apply i).comp continuous_subtype_val).pow (d i))⟩
    exact (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ f).integrable ρ
  simp only [MvPolynomial.eval_eq']
  rw [integral_finset_sum P.support (fun d _ => hint μ d),
    integral_finset_sum P.support (fun d _ => hint ν d)]
  apply Finset.sum_congr rfl
  intro d _
  rw [integral_const_mul, integral_const_mul, hpowers]

/-- For probability measures only the strictly positive tensor orders are
needed; the missing degree-zero moment is their common total mass one. -/
theorem probabilityMeasure_eq_of_compact_positive_tensor_integrals (n : ℕ)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    {μ ν : Measure K} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (heq : ∀ (r : ℕ), 0 < r → ∀ indices : Fin r → Fin n,
      ∫ x : K, (∏ j, x.val (indices j)) ∂μ =
        ∫ x : K, (∏ j, x.val (indices j)) ∂ν) : μ = ν := by
  apply measure_eq_of_compact_tensor_integrals n K hK
  intro r indices
  cases r with
  | zero => simp
  | succ r => exact heq (r + 1) (Nat.succ_pos r) indices

/-- Ordered tensor moments determine ambient finite measures with common
compact support. This is the form needed for normalized uniform measures on
two compact bodies in the same Euclidean coordinate space. -/
theorem measure_eq_of_supported_compact_tensor_integrals (n : ℕ)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    {μ ν : Measure (Fin n → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ Kᶜ = 0) (hν : ν Kᶜ = 0)
    (heq : ∀ (r : ℕ) (indices : Fin r → Fin n),
      ∫ x, (∏ j, x (indices j)) ∂μ = ∫ x, (∏ j, x (indices j)) ∂ν) : μ = ν := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hμr : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hμ
  have hνr : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem hν
  have hc : μ.comap (Subtype.val : K → (Fin n → ℝ)) =
      ν.comap (Subtype.val : K → (Fin n → ℝ)) := by
    apply measure_eq_of_compact_tensor_integrals n K hK
    intro r indices
    calc
      ∫ x : K, (∏ j, x.val (indices j)) ∂μ.comap Subtype.val =
          ∫ x, (∏ j, x (indices j)) ∂μ := by
        simpa only [hμr] using
          (integral_subtype_comap (μ := μ) hKm (fun x => ∏ j, x (indices j)))
      _ = ∫ x, (∏ j, x (indices j)) ∂ν := heq r indices
      _ = ∫ x : K, (∏ j, x.val (indices j)) ∂ν.comap Subtype.val := by
        simpa only [hνr] using
          (integral_subtype_comap (μ := ν) hKm (fun x => ∏ j, x (indices j))).symm
  have hm := congrArg (Measure.map (Subtype.val : K → (Fin n → ℝ))) hc
  rwa [map_comap_subtype_coe hKm, map_comap_subtype_coe hKm, hμr, hνr] at hm

/-- Positive-order tensor moments suffice for compactly supported ambient
probability measures. In particular no symmetry is needed to discard order zero. -/
theorem probabilityMeasure_eq_of_supported_compact_positive_tensor_integrals (n : ℕ)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    {μ ν : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ Kᶜ = 0) (hν : ν Kᶜ = 0)
    (heq : ∀ (r : ℕ), 0 < r → ∀ indices : Fin r → Fin n,
      ∫ x, (∏ j, x (indices j)) ∂μ = ∫ x, (∏ j, x (indices j)) ∂ν) : μ = ν := by
  apply measure_eq_of_supported_compact_tensor_integrals n K hK hμ hν
  intro r indices
  cases r with
  | zero => simp
  | succ r => exact heq (r + 1) (Nat.succ_pos r) indices

section ScalarSupport

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- Multiplying a measure by a nonzero extended nonnegative constant preserves
its support. This makes the normalization in the paper harmless for support. -/
theorem support_smul_of_ne_zero (μ : Measure X) (c : ℝ≥0∞) (hc : c ≠ 0) :
    (c • μ).support = μ.support := by
  have hcpos : 0 < c := pos_iff_ne_zero.mpr hc
  ext x
  simp only [Measure.mem_support_iff_forall, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_pos_iff, hcpos, true_and]

end ScalarSupport

section Supports

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- The support of the restriction of an everywhere-positive measure to a
regular closed set is exactly that set. Star bodies satisfy the regular-closed
condition; convexity and central symmetry are irrelevant to this argument. -/
theorem support_restrict_eq_of_closure_interior
    (μ : Measure X) [μ.IsOpenPosMeasure] (S : Set X)
    (hS : closure (interior S) = S) : (μ.restrict S).support = S := by
  have hSclosed : IsClosed S := hS ▸ isClosed_closure
  apply Set.Subset.antisymm
  · exact (Measure.support_restrict_subset (μ := μ)).trans
      (Set.inter_subset_left.trans hSclosed.closure_eq.le)
  · have hlow : closure (interior S) ⊆ (μ.restrict S).support := by
      apply closure_minimal _ Measure.isClosed_support
      simpa [Measure.support_eq_univ] using
        (Measure.interior_inter_support (μ := μ) (s := S))
    rwa [hS] at hlow

/-- Equality of full-support restrictions identifies the actual sets, including
their boundaries, rather than only proving equality almost everywhere. -/
theorem set_eq_of_restrict_measure_eq
    (μ : Measure X) [μ.IsOpenPosMeasure] (S T : Set X)
    (hS : closure (interior S) = S) (hT : closure (interior T) = T)
    (heq : μ.restrict S = μ.restrict T) : S = T := by
  calc
    S = (μ.restrict S).support := (support_restrict_eq_of_closure_interior μ S hS).symm
    _ = (μ.restrict T).support := congrArg Measure.support heq
    _ = T := support_restrict_eq_of_closure_interior μ T hT

/-- The normalized uniform measures identify regular closed bodies exactly.
Finite positive-volume star bodies meet these hypotheses, without symmetry. -/
theorem set_eq_of_normalized_restrict_measure_eq
    (μ : Measure X) [μ.IsOpenPosMeasure] (S T : Set X)
    (hS : closure (interior S) = S) (hT : closure (interior T) = T)
    (hSf : μ S ≠ ⊤) (hTf : μ T ≠ ⊤)
    (heq : (μ S)⁻¹ • μ.restrict S = (μ T)⁻¹ • μ.restrict T) : S = T := by
  have hsupp := congrArg Measure.support heq
  rw [support_smul_of_ne_zero _ _ (ENNReal.inv_ne_zero.mpr hSf),
    support_smul_of_ne_zero _ _ (ENNReal.inv_ne_zero.mpr hTf),
    support_restrict_eq_of_closure_interior μ S hS,
    support_restrict_eq_of_closure_interior μ T hT] at hsupp
  exact hsupp

end Supports

/-- The full moment-separation implication used for the stabilizer in Lemma
2.1: normalized positive-order tensor moments determine a compact regular
closed body, without assuming central symmetry or convexity. -/
theorem set_eq_of_normalized_positive_tensor_integrals (n : ℕ)
    (μ : Measure (Fin n → ℝ)) [μ.IsOpenPosMeasure] (S T : Set (Fin n → ℝ))
    (hSc : IsCompact S) (hTc : IsCompact T)
    (hS : closure (interior S) = S) (hT : closure (interior T) = T)
    (hS0 : μ S ≠ 0) (hT0 : μ T ≠ 0) (hSf : μ S ≠ ⊤) (hTf : μ T ≠ ⊤)
    (heq : ∀ (r : ℕ), 0 < r → ∀ indices : Fin r → Fin n,
      ∫ x, (∏ j, x (indices j)) ∂((μ S)⁻¹ • μ.restrict S) =
        ∫ x, (∏ j, x (indices j)) ∂((μ T)⁻¹ • μ.restrict T)) : S = T := by
  let νS : Measure (Fin n → ℝ) := (μ S)⁻¹ • μ.restrict S
  let νT : Measure (Fin n → ℝ) := (μ T)⁻¹ • μ.restrict T
  letI : IsProbabilityMeasure νS := ⟨by
    change ((μ S)⁻¹ • μ.restrict S) Set.univ = 1
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hS0 hSf⟩
  letI : IsProbabilityMeasure νT := ⟨by
    change ((μ T)⁻¹ • μ.restrict T) Set.univ = 1
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hT0 hTf⟩
  let K := S ∪ T
  have hK : IsCompact K := hSc.union hTc
  have hKm : MeasurableSet Kᶜ := hK.isClosed.measurableSet.compl
  have hνS : νS Kᶜ = 0 := by
    change ((μ S)⁻¹ • μ.restrict S) Kᶜ = 0
    rw [Measure.smul_apply, Measure.restrict_apply hKm]
    have hempty : Kᶜ ∩ S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.1 (Or.inl hx.2)
    rw [hempty, measure_empty, smul_zero]
  have hνT : νT Kᶜ = 0 := by
    change ((μ T)⁻¹ • μ.restrict T) Kᶜ = 0
    rw [Measure.smul_apply, Measure.restrict_apply hKm]
    have hempty : Kᶜ ∩ T = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.1 (Or.inr hx.2)
    rw [hempty, measure_empty, smul_zero]
  have hmeq : νS = νT :=
    probabilityMeasure_eq_of_supported_compact_positive_tensor_integrals n K hK hνS hνT heq
  exact set_eq_of_normalized_restrict_measure_eq μ S T hS hT hSf hTf hmeq

end BanachIsometric
