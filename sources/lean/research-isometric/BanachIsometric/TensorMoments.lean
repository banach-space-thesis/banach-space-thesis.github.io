import BanachIsometric.UniformBodyMeasure
import BanachIsometric.FiniteEquations
import BanachIsometric.MomentSeparation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FunProp

/-!
# Actual tensor moments of a body and their matrix transformation

Full ordered tensor-coordinate arrays are used in place of symmetric tensors.
Their entries are the same scalar integrals and include odd degrees. This
connects the finite polynomial equations to the actual measures of the bodies.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped ENNReal

/-- The full ordered tensor moment of a measure on real coordinate space. -/
noncomputable def tensorMoment {m : ℕ} (μ : Measure (Fin m → ℝ)) (r : ℕ)
    (indices : Fin r → Fin m) : ℝ := ∫ x, ∏ k, x (indices k) ∂μ

/-- The paper's normalised body moment, in full tensor coordinates. -/
noncomputable def bodyTensorMoment {m : ℕ} (μ : Measure (Fin m → ℝ))
    (S : Set (Fin m → ℝ)) (r : ℕ) : (Fin r → Fin m) → ℝ :=
  tensorMoment (normalizedRestriction μ S) r

theorem integrable_of_supported_compact {X : Type*} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (K : Set X) (hK : IsCompact K) (hμ : μ Kᶜ = 0)
    (f : X → ℝ) (hf : Continuous f) : Integrable f μ := by
  have hr : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hμ
  have hi := hf.continuousOn.integrableOn_compact hK (μ := μ)
  simpa only [IntegrableOn, hr] using hi

/-- Integration commutes with the finite tensor-coordinate expansion. -/
theorem tensorCoordinateAction_tensorMoment {m r : ℕ}
    (μ : Measure (Fin m → ℝ)) (A : Matrix (Fin m) (Fin m) ℝ)
    (hint : ∀ indices : Fin r → Fin m, Integrable (fun x => ∏ k, x (indices k)) μ)
    (out : Fin r → Fin m) :
    tensorCoordinateAction A (tensorMoment μ r) out =
      ∫ x, ∏ k : Fin r, ∑ j : Fin m, A (out k) j * x j ∂μ := by
  have hpoint (x : Fin m → ℝ) :
      (∏ k : Fin r, ∑ j : Fin m, A (out k) j * x j) =
        ∑ inp : Fin r → Fin m, (∏ k, x (inp k)) * ∏ k, A (out k) (inp k) :=
    (tensorCoordinateAction_pure A (fun _ => x) out).symm
  simp only [tensorCoordinateAction, tensorMoment]
  simp_rw [hpoint]
  rw [integral_finset_sum Finset.univ (fun inp _ => (hint inp).mul_const _)]
  simp_rw [integral_mul_const]

/-- The full moment transformation rule for a real linear isomorphism. -/
theorem tensorMoment_map_linearEquiv {m r : ℕ}
    (μ : Measure (Fin m → ℝ)) (e : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hint : ∀ indices : Fin r → Fin m, Integrable (fun x => ∏ k, x (indices k)) μ)
    (out : Fin r → Fin m) :
    tensorMoment (μ.map e) r out =
      tensorCoordinateAction (LinearMap.toMatrix' e.toLinearMap) (tensorMoment μ r) out := by
  rw [tensorCoordinateAction_tensorMoment μ _ hint out]
  unfold tensorMoment
  calc
    (∫ x, ∏ k, x (out k) ∂μ.map e) = ∫ x, ∏ k, (e x) (out k) ∂μ :=
      integral_map_equiv e.toHomeomorph.toMeasurableEquiv (fun x => ∏ k, x (out k))
    _ = _ := by
      congr 1
      funext x
      apply Finset.prod_congr rfl
      intro k _
      simpa only [Matrix.mulVec, dotProduct] using
        congrFun (LinearMap.toMatrix'_mulVec e.toLinearMap x).symm (out k)

/-- Compactness and finite positive volume justify all scalar moment integrals. -/
theorem bodyTensorMoment_integrable {m r : ℕ} (μ : Measure (Fin m → ℝ))
    [μ.IsAddHaarMeasure] (S : Set (Fin m → ℝ)) (hS : IsCompact S) (h0 : μ S ≠ 0)
    (indices : Fin r → Fin m) :
    Integrable (fun x => ∏ k, x (indices k)) (normalizedRestriction μ S) := by
  letI : IsProbabilityMeasure (normalizedRestriction μ S) :=
    normalizedRestriction_isProbabilityMeasure μ S h0 hS.measure_ne_top
  exact integrable_of_supported_compact (normalizedRestriction μ S) S hS
    (normalizedRestriction_compl μ S hS.isClosed.measurableSet) _ (by fun_prop)

/-- The actual body transformation rule `M_r(eS)=e^{⊗r}M_r(S)`, derived from
Haar change of variables and finite product expansion. It is not an assumption. -/
theorem bodyTensorMoment_image {m r : ℕ} (μ : Measure (Fin m → ℝ))
    [μ.IsAddHaarMeasure] (S : Set (Fin m → ℝ)) (hS : IsCompact S) (h0 : μ S ≠ 0)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) :
    bodyTensorMoment μ (e '' S) r =
      tensorCoordinateAction (LinearMap.toMatrix' e.toLinearMap) (bodyTensorMoment μ S r) := by
  funext out
  unfold bodyTensorMoment
  rw [← normalizedRestriction_map_linearEquiv μ e S]
  exact tensorMoment_map_linearEquiv _ e (bodyTensorMoment_integrable μ S hS h0) out

/-- All positive tensor moments identify compact regular closed bodies exactly,
including their boundaries. Positive finite masses supply probability measures;
neither central symmetry nor convexity is required. -/
theorem set_eq_of_bodyTensorMoments_eq {m : ℕ} (μ : Measure (Fin m → ℝ))
    [μ.IsAddHaarMeasure] (S T : Set (Fin m → ℝ))
    (hS : IsCompact S) (hT : IsCompact T)
    (hSreg : closure (interior S) = S) (hTreg : closure (interior T) = T)
    (hS0 : μ S ≠ 0) (hT0 : μ T ≠ 0)
    (heq : ∀ r : ℕ, 0 < r → bodyTensorMoment μ S r = bodyTensorMoment μ T r) : S = T := by
  apply set_eq_of_normalized_positive_tensor_integrals m μ S T hS hT hSreg hTreg
    hS0 hT0 hS.measure_ne_top hT.measure_ne_top
  intro r hr indices
  exact congrFun (heq r hr) indices

end BanachIsometric
