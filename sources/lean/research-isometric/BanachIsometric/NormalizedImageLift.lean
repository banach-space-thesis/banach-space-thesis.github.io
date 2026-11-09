import BanachIsometric.NormalizedImageMoments

/-!
# Exact local lifts after covariance normalization

The varying normalization is retained in the actual image bodies. Moment
regularity of those images is derived by tensor transport, and the normalized
body lifting theorem then applies. The radial specialization discharges all
moment regularity premises by homothetic-shell estimates on the original bodies.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

variable {P : Type*} [PseudoMetricSpace P]

theorem exists_lipschitz_normalized_image_lift {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : P → Set (EuclideanSpace ℝ (Fin m))) (hcompact : ∀ a, IsCompact (S a))
    (h0 : ∀ a, μ (S a) ≠ 0)
    (a₀ : P) (hreg : closure (interior (S a₀)) = S a₀)
    (hinterior : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (S a₀))
    (e : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (heLip : ∃ V ∈ 𝓝 a₀, ∃ K : ℝ≥0,
      LipschitzOnWith K (fun a => (e a).toContinuousLinearMap) V)
    (hcov : ∀ a, covarianceOperator μ (e a '' S a) = ContinuousLinearMap.id ℝ _)
    (hequiv : ∀ a, ∃ d : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      d '' S a₀ = S a)
    (hmom : ∀ I : Finset ℕ+, ∃ V ∈ 𝓝 a₀, ∃ K : ℝ≥0,
      LipschitzOnWith K (fun a =>
        bodyTensorTuple (coordinateMeasure μ) (coordinateBody (S a)) I) V) :
    ∃ q : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      ∃ U : Set P, ∃ K : ℝ≥0, IsOpen U ∧ a₀ ∈ U ∧
        q a₀ = ContinuousLinearEquiv.refl ℝ _ ∧
        LipschitzOnWith K (fun a => (q a).toContinuousLinearMap) U ∧
        ∀ a ∈ U, q a '' (e a₀ '' S a₀) = e a '' S a := by
  let T : P → Set (EuclideanSpace ℝ (Fin m)) := fun a => e a '' S a
  have hTcompact : ∀ a, IsCompact (T a) := fun a => (hcompact a).image (e a).continuous
  have hTreg : closure (interior (T a₀)) = T a₀ := by
    change closure (interior ((e a₀).toHomeomorph '' S a₀)) = _
    rw [← (e a₀).toHomeomorph.image_interior, ← (e a₀).toHomeomorph.image_closure, hreg]
    rfl
  have hTinterior : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (T a₀) := by
    change (0 : EuclideanSpace ℝ (Fin m)) ∈ interior ((e a₀).toHomeomorph '' S a₀)
    rw [← (e a₀).toHomeomorph.image_interior]
    exact ⟨0, hinterior, map_zero (e a₀)⟩
  have hT0 : μ (T a₀) ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds μ (mem_interior_iff_mem_nhds.mp hTinterior)).ne'
  have hTequiv : ∀ a, ∃ d : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      d '' T a₀ = T a := by
    intro a
    obtain ⟨d, hd⟩ := hequiv a
    refine ⟨(e a₀).symm.trans (d.trans (e a)), ?_⟩
    change ((e a₀).symm.trans (d.trans (e a))) '' (e a₀ '' S a₀) = e a '' S a
    calc
      _ = e a '' (d '' ((e a₀).symm '' (e a₀ '' S a₀))) := by
        simp only [image_image]
        rfl
      _ = e a '' (d '' S a₀) := by rw [ContinuousLinearEquiv.symm_image_image]
      _ = T a := by rw [hd]
  have hTmom : ∀ I : Finset ℕ+, ∃ V ∈ 𝓝 a₀, ∃ K : ℝ≥0,
      LipschitzOnWith K (fun a => bodyTensorTuple (coordinateMeasure μ) (coordinateBody (T a)) I) V :=
    fun I => exists_lipschitz_coordinateBody_image_tuple μ S hcompact h0 e a₀ heLip I (hmom I)
  exact exists_lipschitz_normalized_body_lift μ T hTcompact a₀ hTreg hT0 hcov hTequiv hTmom

/-- A radial family with uniform radii and parameter Lipschitz regularity has
an exact locally operator-Lipschitz lift after its actual covariance
normalization. The transformed radii are never identified with the originals.
-/
theorem exists_lipschitz_normalized_radial_image_lift {m : ℕ}
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
    ∃ q : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      ∃ U : Set P, ∃ K : ℝ≥0, IsOpen U ∧ a₀ ∈ U ∧
        q a₀ = ContinuousLinearEquiv.refl ℝ _ ∧
        LipschitzOnWith K (fun a => (q a).toContinuousLinearMap) U ∧
        ∀ a ∈ U, q a '' (e a₀ '' radialBody (ρ a₀)) = e a '' radialBody (ρ a) := by
  have h0 : ∀ a, μ (radialBody (ρ a)) ≠ 0 := by
    intro a
    have hm := radialBody_mass_lower μ (hcompact a) hr (hlo a)
    exact (ENNReal.toReal_pos_iff.mp (hm.1.trans_le hm.2)).1.ne'
  have hinterior : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (radialBody (ρ a₀)) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      (Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin m)) hr)
      (closedBall_subset_radialBody (hlo a₀)))
  have hmom : ∀ I : Finset ℕ+, ∃ V ∈ 𝓝 a₀, ∃ K : ℝ≥0,
      LipschitzOnWith K (fun a => bodyTensorTuple (coordinateMeasure μ)
        (coordinateBody (radialBody (ρ a))) I) V := by
    intro I
    obtain ⟨K, hK⟩ := exists_lipschitz_coordinateBody_tuple_radial_family μ ρ hcompact
      hr hR hlo hhi hparam I
    exact ⟨univ, univ_mem, K, hK.lipschitzOnWith⟩
  exact exists_lipschitz_normalized_image_lift μ (fun a => radialBody (ρ a)) hcompact h0
    a₀ hreg hinterior e heLip hcov hequiv hmom

end
end BanachIsometric
