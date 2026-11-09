import BanachIsometric.OriginalBodyLift
import BanachIsometric.CovarianceNormalization

/-!
# Exact locally Lipschitz equivalences of a radial family

Covariance normalization, finite actual moment tuples, the explicit orthogonal
orbit section, and inversion of the normalization are all constructed. The
result concerns the original radial bodies in their original Euclidean space.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

variable {P : Type*} [PseudoMetricSpace P]

/-- A uniformly positive bounded radial family depending uniformly
Lipschitz-continuously on its parameter admits exact local operator-Lipschitz
body equivalences, whenever its members are real-linearly equivalent. The
reference body is regular closed. No convexity or central symmetry is used.
-/
theorem exists_lipschitz_radial_family_lift {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (ρ : P → EuclideanSpace ℝ (Fin m) → ℝ)
    (hcompact : ∀ a, IsCompact (radialBody (ρ a)))
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlo : ∀ a u, ‖u‖ = 1 → r ≤ ρ a u)
    (hhi : ∀ a u, ‖u‖ = 1 → ρ a u ≤ R)
    {L : ℝ≥0} (hparam : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a => ρ a u))
    (a₀ : P) (hreg : closure (interior (radialBody (ρ a₀))) = radialBody (ρ a₀))
    (hequiv : ∀ a, ∃ d : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      d '' radialBody (ρ a₀) = radialBody (ρ a)) :
    ∃ d : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      ∃ U : Set P, ∃ K : ℝ≥0, IsOpen U ∧ a₀ ∈ U ∧
        d a₀ = ContinuousLinearEquiv.refl ℝ _ ∧
        LipschitzOnWith K (fun a => (d a).toContinuousLinearMap) U ∧
        ∀ a ∈ U, d a '' radialBody (ρ a₀) = radialBody (ρ a) := by
  classical
  obtain ⟨e, V, KE, hV, ha₀V, heLip, heCov⟩ :=
    exists_lipschitz_covarianceNormalization_radial_family μ ρ hcompact hr hR hlo hhi hparam a₀
  let aV : V := ⟨a₀, ha₀V⟩
  let ρV : V → EuclideanSpace ℝ (Fin m) → ℝ := fun a => ρ a.val
  let eV : V → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) := fun a => e a.val
  have hparamV : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a : V => ρV a u) := by
    intro u hu
    simpa only [mul_one] using (hparam u hu).comp
      (isometry_subtype_coe.lipschitz : LipschitzWith 1 (fun a : V => (a : P)))
  have heVLip : LipschitzWith KE (fun a : V => (eV a).toContinuousLinearMap) :=
    heLip.to_restrict
  obtain ⟨dV, W, KD, hW, haVW, hdV0, hdVLip, hdVImage⟩ :=
    exists_lipschitz_radial_family_lift_with_normalizers μ ρV
      (fun a => hcompact a.val) hr hR (fun a => hlo a.val) (fun a => hhi a.val)
      hparamV aV hreg eV ⟨univ, univ_mem, KE, heVLip.lipschitzOnWith⟩
      (fun a => heCov a.val a.property) (fun a => hequiv a.val)
  let d : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun a => if ha : a ∈ V then dV ⟨a, ha⟩ else ContinuousLinearEquiv.refl ℝ _
  let U : Set P := Subtype.val '' W
  have hU : IsOpen U := hV.isOpenMap_subtype_val W hW
  have ha₀U : a₀ ∈ U := ⟨aV, haVW, rfl⟩
  refine ⟨d, U, KD, hU, ha₀U, ?_, ?_, ?_⟩
  · simpa only [d, dif_pos ha₀V] using hdV0
  · apply LipschitzOnWith.of_dist_le_mul
    rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
    simpa only [d, dif_pos a'.property, dif_pos b'.property] using
      hdVLip.dist_le_mul a' ha' b' hb'
  · rintro a ⟨a', ha', rfl⟩
    simpa only [d, dif_pos a'.property] using hdVImage a' ha'

end
end BanachIsometric
