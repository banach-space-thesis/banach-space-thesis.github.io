import BanachIsometric.ExactFamilyTheorem
import BanachIsometric.ExactFamilyAmbientQuadratic
import BanachIsometric.ContinuousSphereDegreeSurjective

/-!
# Ambient ellipsoid conclusion with a merely continuous normal map

This closes the analytic and pair-coverage implication with exactly the
normal regularity in the paper. The nonzero-degree exact family remains
the explicit input; constructing it is the bundle-annihilation obligation.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped NNReal

theorem gauge_sublevel_eq_quadratic_sublevel
    {V : Type*} [AddCommGroup V] [Module ℝ V] {g : V → ℝ}
    (hnonneg : ∀ x, 0 ≤ g x) (Q : QuadraticForm ℝ V) (hQ : ∀ x, Q x = g x ^ 2) :
    {x | g x ≤ 1} = {x | Q x ≤ 1} := by
  ext x
  change g x ≤ 1 ↔ Q x ≤ 1
  rw [hQ]
  constructor <;> intro h <;> nlinarith [hnonneg x]

namespace ExactTangentialFamily

variable {m N : ℕ} [NeZero N]
  {g : EuclideanSpace ℝ (Fin N) → ℝ} {p : EuclideanSpace ℝ (Fin m) → ℝ}
  (A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin N)) g p)

theorem exists_posDef_ambient_quadraticForm_of_nonzero_continuousNormalDegree
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hEven : Even N) (hdegree : A.continuousNormalDegree e ≠ 0)
    (H : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 → Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (hRange : ∀ z, Set.range (A.maps z) = (H (A.normal z) : Set (EuclideanSpace ℝ (Fin N))))
    (hpair : ∀ x y, ∃ u, x ∈ H u ∧ y ∈ H u) :
    ∃ R : QuadraticForm ℝ (EuclideanSpace ℝ (Fin N)), R.PosDef ∧
      (∀ x, R x = g x ^ 2) ∧ {x | g x ≤ 1} = {x | R x ≤ 1} := by
  obtain ⟨Q, _hQpos, hQ⟩ := A.exists_posDef_quadraticForm_of_nonzero_continuousNormalDegree
    μ e hp hg hcont hEven hdegree
  have hnormal : Function.Surjective A.normal :=
    continuousSphereSignedDegree_surjective_of_ne_zero e A.normal hdegree
  have hpairs : ∀ x y, ∃ z, x ∈ Set.range (A.maps z) ∧ y ∈ Set.range (A.maps z) := by
    intro x y
    obtain ⟨u, hx, hy⟩ := hpair x y
    obtain ⟨z, hz⟩ := hnormal u
    refine ⟨z, ?_, ?_⟩
    · rwa [hRange z, hz]
    · rwa [hRange z, hz]
  obtain ⟨R, hRpos, hR⟩ := A.exists_posDef_ambient_quadraticForm_of_pairwise_range hg hcont Q hQ hpairs
  exact ⟨R, hRpos, hR, gauge_sublevel_eq_quadratic_sublevel hg.nonneg R hR⟩

end ExactTangentialFamily
end BanachIsometric
