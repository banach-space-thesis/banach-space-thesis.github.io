import BanachIsometric.BodyComponentTransport

/-! Actual conjugation of body automorphisms transports the inherited
operator-unit topology. This removes covariance-position hypotheses from
the finite-component result by constructing a genuine covariance normalizer. -/

noncomputable section

namespace BanachIsometric

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bodyAutomorphism_conjugate_mem (e : E ≃L[ℝ] E) (S : Set E)
    (g : bodyAutomorphismGroup S) :
    e.toUnit * g.val * e.toUnit⁻¹ ∈ bodyAutomorphismGroup (e '' S) := by
  change (e ∘ (g.val : E →L[ℝ] E) ∘ e.symm) '' (e '' S) = e '' S
  rw [Set.image_comp, Set.image_comp, e.symm_image_image, g.property]

def bodyAutomorphismConjugation (e : E ≃L[ℝ] E) (S T : Set E) (he : e '' S = T) :
    bodyAutomorphismGroup S ≃* bodyAutomorphismGroup T where
  toFun g := ⟨e.toUnit * g.val * e.toUnit⁻¹, by
    rw [← he]
    exact bodyAutomorphism_conjugate_mem e S g⟩
  invFun g := ⟨e.toUnit⁻¹ * g.val * e.toUnit, by
    have hinv : e.symm '' T = S := by rw [← he, e.symm_image_image]
    rw [← hinv]
    exact bodyAutomorphism_conjugate_mem e.symm T g⟩
  left_inv g := by apply Subtype.ext; simp [mul_assoc]
  right_inv g := by apply Subtype.ext; simp [mul_assoc]
  map_mul' g h := by apply Subtype.ext; simp [mul_assoc]

def bodyAutomorphismConjugationHomeomorph (e : E ≃L[ℝ] E)
    (S T : Set E) (he : e '' S = T) :
    bodyAutomorphismGroup S ≃ₜ bodyAutomorphismGroup T where
  toEquiv := (bodyAutomorphismConjugation e S T he).toEquiv
  continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- A continuous multiplicative equivalence preserves the actual connected
identity component. -/
theorem preimage_connectedComponentOfOne_of_mulEquiv
    {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃* H) (he : Continuous e) (hi : Continuous e.symm) :
    e ⁻¹' (Subgroup.connectedComponentOfOne H : Set H) =
      (Subgroup.connectedComponentOfOne G : Set G) := by
  ext g
  change e g ∈ connectedComponent (1 : H) ↔ g ∈ connectedComponent (1 : G)
  constructor
  · intro hg
    have h := hi.mapsTo_connectedComponent (1 : H) hg
    simpa only [e.symm_apply_apply, e.symm.map_one] using h
  · intro hg
    have h := he.mapsTo_connectedComponent (1 : G) hg
    simpa only [e.map_one] using h

/-- Compact regular closed Euclidean bodies with an interior origin have an
open identity component in their actual operator-unit automorphism group. -/
theorem isOpen_bodyAutomorphismGroup_connectedComponent_of_interior {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    IsOpen (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) :
      Set (bodyAutomorphismGroup S)) := by
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
  let f := bodyAutomorphismConjugation e S T rfl
  let fH := bodyAutomorphismConjugationHomeomorph e S T rfl
  have hopen := isOpen_bodyAutomorphismGroup_connectedComponent
    (μ := μ) (S := T) (hS := hT) (hC := he) hTreg hμT
  rw [← preimage_connectedComponentOfOne_of_mulEquiv f fH.continuous fH.symm.continuous]
  exact hopen.preimage fH.continuous

/-- The genuine operator-unit automorphism group of a compact Euclidean
body containing the origin in its interior is compact. -/
theorem compactSpace_bodyAutomorphismGroup_of_interior {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    CompactSpace (bodyAutomorphismGroup S) := by
  obtain ⟨e, he⟩ := exists_covariancePosition μ hS h0
  let T := e '' S
  letI := compactSpace_bodyAutomorphismGroup (μ := μ) (S := T)
    (hS := hS.image e.continuous) (hC := he)
  exact (bodyAutomorphismConjugationHomeomorph e S T rfl).symm.compactSpace

/-- Finitely many actual connected components, with covariance position
constructed rather than assumed. -/
theorem finite_bodyAutomorphismGroup_componentQuotient_of_interior {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    Finite ((bodyAutomorphismGroup S) ⧸
      Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) := by
  letI := compactSpace_bodyAutomorphismGroup_of_interior μ S hS h0
  exact Subgroup.quotient_finite_of_isOpen _
    (isOpen_bodyAutomorphismGroup_connectedComponent_of_interior μ S hS hreg h0)

end BanachIsometric
