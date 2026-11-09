import SurveyStatements.P1Transfer
import SurveyStatements.P1BasicSequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Tactic.FieldSimp

/-!
Finite norming families and the finite-codimension selection step for a
basic-sequence construction. These are unconditional kernel proofs.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A finite-dimensional subspace admits a finite family of norm-one ambient
functionals which almost norm each nonzero vector. No completeness is needed. -/
theorem finite_norming_family (M : Submodule ℂ X) [FiniteDimensional ℂ M]
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ F : Finset (X →L[ℂ] ℂ), (∀ f ∈ F, ‖f‖ = 1) ∧
      ∀ x ∈ M, x ≠ 0 → ∃ f ∈ F, c * ‖x‖ < ‖f x‖ := by
  classical
  let D := {f : X →L[ℂ] ℂ // ‖f‖ = 1}
  let U : D → Set M := fun f => {x | c < ‖f.1 x‖}
  have hU : ∀ f, IsOpen (U f) := by
    intro f
    exact isOpen_lt continuous_const
      (f.1.continuous.comp continuous_subtype_val).norm
  have hcover : Metric.sphere (0 : M) 1 ⊆ ⋃ f, U f := by
    intro x hx
    have hxnorm : ‖(x : X)‖ = 1 := by simpa using hx
    have hx0 : (x : X) ≠ 0 := by
      intro h
      simpa [h] using hxnorm
    obtain ⟨f, hfnorm, hf⟩ := exists_dual_vector ℂ (x : X) hx0
    refine Set.mem_iUnion.mpr ⟨⟨f, hfnorm⟩, ?_⟩
    change c < ‖f (x : X)‖
    simpa [hf, hxnorm] using hc1
  obtain ⟨A, hA⟩ := (isCompact_sphere (0 : M) 1).elim_finite_subcover U hU hcover
  refine ⟨A.image Subtype.val, ?_, ?_⟩
  · intro f hf
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hf
    exact g.2
  · intro x hx hx0
    let y : M := ⟨unitNormalize x, M.smul_mem _ hx⟩
    have hy : y ∈ Metric.sphere (0 : M) 1 := by
      simpa [y] using norm_unitNormalize hx0
    obtain ⟨f, hfA, hyf⟩ := Set.mem_iUnion₂.mp (hA hy)
    refine ⟨f.1, Finset.mem_image.mpr ⟨f, hfA, rfl⟩, ?_⟩
    have hynorm : c < ‖f.1 (unitNormalize x)‖ := hyf
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hscale := mul_lt_mul_of_pos_right hynorm hxpos
    have heq : ‖f.1 (unitNormalize x)‖ * ‖x‖ = ‖f.1 x‖ := by
      calc
        ‖f.1 (unitNormalize x)‖ * ‖x‖ =
            ‖f.1 ((‖x‖ : ℂ) • unitNormalize x)‖ := by
              simp [norm_smul, mul_comm]
        _ = ‖f.1 x‖ := by rw [norm_smul_unitNormalize]
    rwa [heq] at hscale

/-- Finitely many functionals cannot separate points of an infinite-dimensional
space. Their common kernel therefore contains a nonzero vector. -/
theorem finite_functionals_common_kernel (hX : ¬ FiniteDimensional ℂ X)
    (F : Finset (X →L[ℂ] ℂ)) :
    ∃ x : X, x ≠ 0 ∧ ∀ f ∈ F, f x = 0 := by
  classical
  by_contra h
  have hz : ∀ x : X, (∀ f ∈ F, f x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    exact h ⟨x, hx0, hx⟩
  let T : X →ₗ[ℂ] (F → ℂ) := LinearMap.pi fun f => f.1.toLinearMap
  have hT : Function.Injective T := by
    intro x y hxy
    have hzero : x - y = 0 := hz (x - y) (by
      intro f hf
      have heq := congrFun hxy ⟨f, hf⟩
      simpa [T, map_sub] using sub_eq_zero.mpr heq)
    exact sub_eq_zero.mp hzero
  exact hX (FiniteDimensional.of_injective T hT)

/-- The common kernel can be met on the unit sphere. -/
theorem finite_functionals_unit_kernel (hX : ¬ FiniteDimensional ℂ X)
    (F : Finset (X →L[ℂ] ℂ)) :
    ∃ x : X, ‖x‖ = 1 ∧ ∀ f ∈ F, f x = 0 := by
  obtain ⟨x, hx0, hxF⟩ := finite_functionals_common_kernel hX F
  refine ⟨unitNormalize x, norm_unitNormalize hx0, ?_⟩
  intro f hf
  simp [unitNormalize, hxF f hf]

/-- A finite norming family controls a vector even after adding any vector in
the family's common kernel. -/
theorem finite_norming_kernel_bound (M : Submodule ℂ X) {c : ℝ} (hc : 0 < c)
    (F : Finset (X →L[ℂ] ℂ))
    (hFnorm : ∀ f ∈ F, ‖f‖ = 1)
    (hF : ∀ x ∈ M, x ≠ 0 → ∃ f ∈ F, c * ‖x‖ < ‖f x‖)
    {x z : X} (hx : x ∈ M) (hz : ∀ f ∈ F, f z = 0) :
    c * ‖x‖ ≤ ‖x + z‖ := by
  by_cases hx0 : x = 0
  · simp [hx0, norm_nonneg]
  obtain ⟨f, hf, hfx⟩ := hF x hx hx0
  have hbound := f.le_opNorm (x + z)
  rw [hFnorm f hf, one_mul, map_add, hz f hf, add_zero] at hbound
  exact hfx.le.trans hbound

/-- The local selection step: a unit vector annihilates the previous family
and a new family which norms the current finite-dimensional span. -/
theorem finite_basic_selection_step (hX : ¬ FiniteDimensional ℂ X)
    (M : Submodule ℂ X) [FiniteDimensional ℂ M]
    (G : Finset (X →L[ℂ] ℂ)) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ (v : X) (F : Finset (X →L[ℂ] ℂ)),
      ‖v‖ = 1 ∧ v ∉ M ∧ (∀ f ∈ G, f v = 0) ∧
      (∀ f ∈ F, ‖f‖ = 1) ∧
      (∀ x ∈ M, x ≠ 0 → ∃ f ∈ F, c * ‖x‖ < ‖f x‖) ∧
      (∀ x ∈ M, ∀ a : ℂ, c * ‖x‖ ≤ ‖x + a • v‖) ∧
      ∀ f ∈ F, f v = 0 := by
  classical
  obtain ⟨F, hFnorm, hF⟩ := finite_norming_family M hc0 hc1
  obtain ⟨v, hvnorm, hv⟩ := finite_functionals_unit_kernel hX (G ∪ F)
  have hv0 : v ≠ 0 := by
    intro h
    simpa [h] using hvnorm
  have hvM : v ∉ M := by
    intro hvm
    obtain ⟨f, hf, hfv⟩ := hF v hvm hv0
    rw [hv f (Finset.mem_union_right G hf), norm_zero, hvnorm, mul_one] at hfv
    exact (not_lt_of_ge hc0.le) hfv
  refine ⟨v, F, hvnorm, hvM, ?_, hFnorm, hF, ?_, ?_⟩
  · intro f hf
    exact hv f (Finset.mem_union_left F hf)
  · intro x hx a
    apply finite_norming_kernel_bound M hc0 F hFnorm hF hx
    intro f hf
    simp [hv f (Finset.mem_union_right G hf)]
  · intro f hf
    exact hv f (Finset.mem_union_right G hf)

end SurveyStatements.P1
