import BanachIsometric.BodyStabilizerRetraction
import BanachIsometric.BodyGroupConjugation

/-! Conjugation transports an actual ambient Lipschitz body-group retraction.
Covariance position is constructed from the body, not added as a hypothesis. -/

namespace BanachIsometric

open Set MeasureTheory
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ambient operator-space conjugation in the original operator norms. -/
def operatorConjugation (e : E ≃L[ℝ] E) : (E →L[ℝ] E) ≃L[ℝ] (E →L[ℝ] E) :=
  e.arrowCongr e

theorem operatorConjugation_apply (e : E ≃L[ℝ] E) (T : E →L[ℝ] E) (x : E) :
    operatorConjugation e T x = e (T (e.symm x)) := rfl

theorem operatorConjugation_mul (e : E ≃L[ℝ] E) (T R : E →L[ℝ] E) :
    operatorConjugation e (T * R) = operatorConjugation e T * operatorConjugation e R := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [operatorConjugation_apply, ContinuousLinearMap.mul_apply, e.symm_apply_apply]

theorem operatorConjugation_body_image (e : E ≃L[ℝ] E) (T : E →L[ℝ] E) (S : Set E) :
    operatorConjugation e T '' (e '' S) = e '' (T '' S) := by
  change (e ∘ T ∘ e.symm) '' (e '' S) = e '' (T '' S)
  rw [image_comp, image_comp, e.symm_image_image]

theorem operatorConjugation_isUnit (e : E ≃L[ℝ] E) (T : E →L[ℝ] E)
    (hT : IsUnit T) : IsUnit (operatorConjugation e T) := by
  obtain ⟨u, rfl⟩ := hT
  exact ⟨e.toUnit * u * e.toUnit⁻¹, rfl⟩

theorem operatorConjugation_bodyAutomorphism (e : E ≃L[ℝ] E) (S T : Set E)
    (he : e '' S = T) (g : bodyAutomorphismGroup S) :
    ((bodyAutomorphismConjugation e S T he g).val : E →L[ℝ] E) =
      operatorConjugation e (g.val : E →L[ℝ] E) := rfl

/-- A retraction in the ambient real operator space, with exact left equivariance.
Its values are actual invertible body-preserving operators on the stated domain. -/
structure AmbientBodyRetraction (S : Set E) where
  domain : Set (E →L[ℝ] E)
  retract : (E →L[ℝ] E) → (E →L[ℝ] E)
  constant : ℝ≥0
  isOpen_domain : IsOpen domain
  lipschitz : LipschitzOnWith constant retract domain
  contains : ∀ g : bodyAutomorphismGroup S, (g.val : E →L[ℝ] E) ∈ domain
  range : ∀ T ∈ domain, IsUnit (retract T) ∧ retract T '' S = S
  fixes : ∀ g : bodyAutomorphismGroup S, retract (g.val : E →L[ℝ] E) = (g.val : E →L[ℝ] E)
  equivariant : ∀ g : bodyAutomorphismGroup S, ∀ T,
    retract ((g.val : E →L[ℝ] E) * T) = (g.val : E →L[ℝ] E) * retract T
  invariant : ∀ g : bodyAutomorphismGroup S, ∀ T ∈ domain, (g.val : E →L[ℝ] E) * T ∈ domain

/-- Pull an ambient retraction back along a fixed actual body equivalence. -/
def AmbientBodyRetraction.transport {S T : Set E} (D : AmbientBodyRetraction T)
    (e : E ≃L[ℝ] E) (he : e '' S = T) : AmbientBodyRetraction S := by
  let C := operatorConjugation e
  let r : (E →L[ℝ] E) → (E →L[ℝ] E) := fun A => C.symm (D.retract (C A))
  have hCmul (A B : E →L[ℝ] E) : C (A * B) = C A * C B := operatorConjugation_mul e A B
  have hCim (A B : E →L[ℝ] E) : C.symm (A * B) = C.symm A * C.symm B :=
    operatorConjugation_mul e.symm A B
  let φ := bodyAutomorphismConjugation e S T he
  have hφ (g : bodyAutomorphismGroup S) : (φ g).val.val = C g.val.val := rfl
  refine ⟨C ⁻¹' D.domain, r,
    ‖C.symm.toContinuousLinearMap‖₊ * (D.constant * ‖C.toContinuousLinearMap‖₊),
    D.isOpen_domain.preimage C.continuous, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact C.symm.lipschitz.lipschitzOnWith.comp
      (D.lipschitz.comp C.lipschitz.lipschitzOnWith (fun _ h => h)) (fun _ _ => mem_univ _)
  · intro g
    change C g.val.val ∈ D.domain
    rw [← hφ g]
    exact D.contains (φ g)
  · intro A hA
    obtain ⟨hunit, hbody⟩ := D.range (C A) hA
    refine ⟨operatorConjugation_isUnit e.symm _ hunit, ?_⟩
    have hinv : e.symm '' T = S := by rw [← he, e.symm_image_image]
    change C.symm (D.retract (C A)) '' S = S
    rw [← hinv]
    change operatorConjugation e.symm (D.retract (C A)) '' (e.symm '' T) = e.symm '' T
    rw [operatorConjugation_body_image, hbody]
  · intro g
    change C.symm (D.retract (C g.val.val)) = g.val.val
    rw [← hφ g, D.fixes, hφ g, C.symm_apply_apply]
  · intro g A
    change C.symm (D.retract (C (g.val.val * A))) = g.val.val * C.symm (D.retract (C A))
    rw [hCmul, ← hφ g, D.equivariant, hCim, hφ g, C.symm_apply_apply]
  · intro g A hA
    change C (g.val.val * A) ∈ D.domain
    rw [hCmul, ← hφ g]
    exact D.invariant (φ g) _ hA

/-- Every actual compact regular closed Euclidean body with an interior origin
admits an ambient left-equivariant Lipschitz body-group retraction. -/
theorem nonempty_ambientBodyRetraction {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    Nonempty (AmbientBodyRetraction S) := by
  obtain ⟨e, he⟩ := exists_covariancePosition μ hS h0
  let T := e '' S
  have hT : IsCompact T := hS.image e.continuous
  have hTreg : closure (interior T) = T := by
    let eh := e.toHomeomorph
    change closure (interior (eh '' S)) = eh '' S
    rw [← eh.image_interior, ← eh.image_closure, hreg]
  have hT0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior T := by
    rw [show interior T = e '' interior S from (e.toHomeomorph.image_interior S).symm]
    exact ⟨0, h0, e.map_zero⟩
  have hμT : μ T ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds μ (mem_interior_iff_mem_nhds.mp hT0)).ne'
  obtain ⟨U, r, L, hopen, hLip, hcontains, hrange, hfix, hequiv, hinvariant⟩ :=
    exists_ambient_lipschitz_body_retraction_covariancePosition μ T hT he hTreg hμT
  let D : AmbientBodyRetraction T := ⟨U, r, L, hopen, hLip, hcontains, hrange,
    hfix, hequiv, hinvariant⟩
  exact ⟨D.transport e rfl⟩

end
end BanachIsometric
