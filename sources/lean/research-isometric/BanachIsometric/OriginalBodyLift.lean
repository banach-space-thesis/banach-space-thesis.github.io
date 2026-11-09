import BanachIsometric.NormalizedImageLift
import BanachIsometric.LocalInverseFamily

/-!
# Undoing normalization in exact local body lifts

The original-body map is `e(a)⁻¹ q(a) e(a₀)`. Local inversion and composition
estimates prove its operator Lipschitz regularity; all body-image equalities
and the identity at the reference parameter are exact.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

variable {P E : Type*} [PseudoMetricSpace P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_lipschitz_unnormalized_body_lift
    (S : P → Set E) (a₀ : P) (e q : P → E ≃L[ℝ] E)
    (heLip : ∃ V ∈ 𝓝 a₀, ∃ K : ℝ≥0,
      LipschitzOnWith K (fun a => (e a).toContinuousLinearMap) V)
    {U : Set P} (hU : U ∈ 𝓝 a₀) {KQ : ℝ≥0}
    (hqLip : LipschitzOnWith KQ (fun a => (q a).toContinuousLinearMap) U)
    (hq0 : q a₀ = ContinuousLinearEquiv.refl ℝ E)
    (hqImage : ∀ a ∈ U, q a '' (e a₀ '' S a₀) = e a '' S a) :
    ∃ d : P → E ≃L[ℝ] E, ∃ W : Set P, ∃ K : ℝ≥0,
      IsOpen W ∧ a₀ ∈ W ∧ W ⊆ U ∧
        d a₀ = ContinuousLinearEquiv.refl ℝ E ∧
        LipschitzOnWith K (fun a => (d a).toContinuousLinearMap) W ∧
        ∀ a ∈ W, d a '' S a₀ = S a := by
  obtain ⟨V, hV, KE, he⟩ := heLip
  obtain ⟨WI, KI, hWI, ha₀WI, _, hInv⟩ :=
    exists_lipschitzOnWith_symm_continuousLinearEquiv_family e a₀ hV he
  let T := WI ∩ U
  have hT : T ∈ 𝓝 a₀ := inter_mem (hWI.mem_nhds ha₀WI) hU
  obtain ⟨W, KW, hW, ha₀W, hWT, hProd⟩ := exists_lipschitzOnWith_clm_comp_family
    (fun a => (e a).symm.toContinuousLinearMap) (fun a => (q a).toContinuousLinearMap)
    a₀ hT (hInv.mono inter_subset_left) (hqLip.mono inter_subset_right)
  let d : P → E ≃L[ℝ] E := fun a => (e a₀).trans ((q a).trans (e a).symm)
  let R : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).flip (e a₀).toContinuousLinearMap
  refine ⟨d, W, ‖R‖₊ * KW, hW, ha₀W, hWT.trans inter_subset_right, ?_, ?_, ?_⟩
  · apply ContinuousLinearEquiv.ext
    funext x
    change (e a₀).symm (q a₀ (e a₀ x)) = x
    rw [hq0]
    exact (e a₀).symm_apply_apply x
  · have h := R.lipschitz.lipschitzOnWith.comp hProd (fun _ _ => mem_univ _)
    exact h
  · intro a ha
    have hqa := hqImage a ((hWT ha).2)
    calc
      d a '' S a₀ = (e a).symm '' (q a '' (e a₀ '' S a₀)) := by
        simp only [image_image]
        rfl
      _ = (e a).symm '' (e a '' S a) := by rw [hqa]
      _ = S a := ContinuousLinearEquiv.symm_image_image _ _

variable {m : ℕ}

/-- Exact local lifts of the original radial bodies after constructing the
normalized-image orbit section. Covariance normalization and its inverse are
retained as the actual operators in the proof. -/
theorem exists_lipschitz_radial_family_lift_with_normalizers
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (ρ : P → EuclideanSpace ℝ (Fin m) → ℝ)
    (hcompact : ∀ a, IsCompact (radialBody (ρ a)))
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlo : ∀ a u, ‖u‖ = 1 → r ≤ ρ a u)
    (hhi : ∀ a u, ‖u‖ = 1 → ρ a u ≤ R)
    {L : ℝ≥0} (hparam : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a => ρ a u))
    (a₀ : P) (hreg : closure (interior (radialBody (ρ a₀))) = radialBody (ρ a₀))
    (e : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (heLip : ∃ V ∈ 𝓝 a₀, ∃ K : ℝ≥0,
      LipschitzOnWith K (fun a => (e a).toContinuousLinearMap) V)
    (hcov : ∀ a, covarianceOperator μ (e a '' radialBody (ρ a)) = ContinuousLinearMap.id ℝ _)
    (hequiv : ∀ a, ∃ d : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      d '' radialBody (ρ a₀) = radialBody (ρ a)) :
    ∃ d : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      ∃ U : Set P, ∃ K : ℝ≥0, IsOpen U ∧ a₀ ∈ U ∧
        d a₀ = ContinuousLinearEquiv.refl ℝ _ ∧
        LipschitzOnWith K (fun a => (d a).toContinuousLinearMap) U ∧
        ∀ a ∈ U, d a '' radialBody (ρ a₀) = radialBody (ρ a) := by
  obtain ⟨q, U, KQ, hU, ha₀U, hq0, hqLip, hqImage⟩ :=
    exists_lipschitz_normalized_radial_image_lift μ ρ hcompact hr hR hlo hhi hparam
      a₀ hreg e heLip hcov hequiv
  obtain ⟨d, W, KW, hW, ha₀W, _, hd0, hdLip, hdImage⟩ :=
    exists_lipschitz_unnormalized_body_lift (fun a => radialBody (ρ a)) a₀ e q heLip
      (hU.mem_nhds ha₀U) hqLip hq0 hqImage
  exact ⟨d, W, KW, hW, ha₀W, hd0, hdLip, hdImage⟩

end
end BanachIsometric
