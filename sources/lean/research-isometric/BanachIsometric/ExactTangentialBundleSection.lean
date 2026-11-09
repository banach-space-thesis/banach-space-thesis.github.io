import BanachIsometric.ExactSectionLipschitzRegularization
import BanachIsometric.SphereNormalProjection
import BanachIsometric.ExactBodyGauge

/-! A continuous section of the actual bundle gives the exact Lipschitz
tangential family used by the signed-degree argument. The specified normal
map is preserved, and gauge equality is derived from actual body equality. -/

namespace BanachIsometric

open Set MeasureTheory
open scoped NNReal

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

namespace ExactSectionPrincipalData

theorem exists_exactTangentialFamily_of_bundle_section {m : ℕ} {p : F → ℝ}
    {H : Metric.sphere (0 : F) 1 → Submodule ℝ F} {a₀ : Metric.sphere (0 : F) 1}
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (normal : C(Metric.sphere (0 : F) 1, Metric.sphere (0 : F) 1))
    (hTangent : ∀ a, H a ≤ normalHyperplane (normal a))
    {LP : ℝ≥0} (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (σ : Metric.sphere (0 : F) 1 → D.core.TotalSpace) (hσ : Continuous σ)
    (hbase : ∀ a, (σ a).proj = a) :
    ∃ A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) F p (fun x => p (D.reference x)),
      A.normal = normal ∧ ∀ a, Function.Injective (A.maps a) ∧
        LinearMap.range (A.maps a).toLinearMap = H a ∧
        A.maps a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H a : Set F) := by
  obtain ⟨B, L, hBLip, hB⟩ := D.exists_lipschitz_operator_section_of_bundle_section μ
    (isCompact_sphere (0 : F) 1) hp hSphere σ hσ hbase hProj
  have hTangency : ∀ a y, inner ℝ (B a y) (normal a).val = 0 := by
    intro a y
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mp
    exact hTangent a ((hB a).2.1.le (LinearMap.mem_range_self (B a).toLinearMap y))
  have hRange : ∀ a, Set.range (B a) = (H a : Set F) := by
    intro a
    change (LinearMap.range (B a).toLinearMap : Set F) = (H a : Set F)
    rw [(hB a).2.1]
  have hBody : ∀ a, B a '' {x | p (D.reference x) ≤ 1} = {y : F | p y ≤ 1} ∩ Set.range (B a) := by
    intro a
    rw [hRange a]
    exact (hB a).2.2
  let A := exactTangentialFamilyOfBodyMaps (hp.comp_linearIsometry D.reference) hp normal B
    ⟨L, hBLip⟩ (fun a => (hB a).1) hTangency hBody
  exact ⟨A, rfl, hB⟩

/-- For the real orthogonal-hyperplane field, the original Lipschitz normal
map itself supplies the required operator Lipschitz projection estimate. -/
theorem exists_exactTangentialFamily_normalHyperplane_of_bundle_section {m : ℕ} {p : F → ℝ}
    (normal : C(Metric.sphere (0 : F) 1, Metric.sphere (0 : F) 1))
    {a₀ : Metric.sphere (0 : F) 1}
    (D : ExactSectionPrincipalData m p (fun a => normalHyperplane (normal a)) a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    {LN : ℝ≥0} (hNormal : LipschitzWith LN normal)
    (σ : Metric.sphere (0 : F) 1 → D.core.TotalSpace) (hσ : Continuous σ)
    (hbase : ∀ a, (σ a).proj = a) :
    ∃ A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) F p (fun x => p (D.reference x)),
      A.normal = normal ∧ ∀ a, Function.Injective (A.maps a) ∧
        LinearMap.range (A.maps a).toLinearMap = normalHyperplane (normal a) ∧
        A.maps a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (normalHyperplane (normal a) : Set F) :=
  D.exists_exactTangentialFamily_of_bundle_section μ hp hSphere normal (fun _ => le_rfl)
    (lipschitzWith_normalHyperplane_family normal hNormal) σ hσ hbase

end ExactSectionPrincipalData

end
end BanachIsometric
