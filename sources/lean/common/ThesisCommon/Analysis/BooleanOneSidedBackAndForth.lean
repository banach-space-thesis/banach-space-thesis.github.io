import ThesisCommon.Analysis.BooleanDensityBackAndForth
import ThesisCommon.Analysis.BooleanPartialIsometryBase

/-! Two one-generator extensions supply a genuine back-and-forth step.
The square cardinal bound is the actual two-cell normal-form bound. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon
universe u
variable {A B : Type u} [BooleanAlgebra A] [BooleanAlgebra B]
  [MetricSpace A] [MetricSpace B]
open BooleanPartialIsometry

theorem exists_boolean_twoSided_extension
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (forward : ∀ p : BooleanPartialIsometry A B, #p.source < κ → ∀ x : A,
      ∃ q, p ≤ q ∧ x ∈ q.source ∧ #q.source ≤ #p.source * #p.source)
    (backward : ∀ p : BooleanPartialIsometry B A, #p.source < κ → ∀ y : B,
      ∃ q, p ≤ q ∧ y ∈ q.source ∧ #q.source ≤ #p.source * #p.source)
    (p : BooleanPartialIsometry A B) (hp : #p.source < κ) (x : A) (y : B) :
    ∃ q : BooleanPartialIsometry A B, p ≤ q ∧ x ∈ q.source ∧ y ∈ q.target ∧
      #q.source ≤ #p.source * #p.source * #p.source * #p.source := by
  obtain ⟨q, hpq, hx, hq⟩ := forward p hp x
  have hqsmall : #q.source < κ := hq.trans_lt (Cardinal.mul_lt_of_lt hκ hp hp)
  have hqssmall : #q.symm.source < κ := by
    rw [symm_source, cardinal_target_eq_source]
    exact hqsmall
  obtain ⟨r, hqr, hy, hr⟩ := backward q.symm hqssmall y
  have hqrs : q ≤ r.symm := by simpa only [symm_symm] using symm_mono hqr
  refine ⟨r.symm, hpq.trans hqrs, source_mono hqrs hx, hy, ?_⟩
  rw [symm_source, cardinal_target_eq_source]
  rw [symm_source, cardinal_target_eq_source] at hr
  exact hr.trans ((mul_le_mul' hq hq).trans_eq (by ac_rfl))

theorem exists_booleanIsometry_of_oneSided_small_extensions
    [CompleteSpace A] [CompleteSpace B] [ContinuousInf A] [ContinuousInf B]
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hA : topologicalDensity A = κ) (hB : topologicalDensity B = κ)
    (hdist : dist (⊥ : A) ⊤ = dist (⊥ : B) ⊤)
    (forward : ∀ p : BooleanPartialIsometry A B, #p.source < κ → ∀ x : A,
      ∃ q, p ≤ q ∧ x ∈ q.source ∧ #q.source ≤ #p.source * #p.source)
    (backward : ∀ p : BooleanPartialIsometry B A, #p.source < κ → ∀ y : B,
      ∃ q, p ≤ q ∧ y ∈ q.source ∧ #q.source ≤ #p.source * #p.source) :
    ∃ e : A ≃o B, Isometry e :=
  exists_booleanIsometry_of_equal_density_and_small_extensions κ hκ hA hB
    (initial hdist) (initial_source_finite hdist)
    (exists_boolean_twoSided_extension κ hκ forward backward)

end ThesisCommon
