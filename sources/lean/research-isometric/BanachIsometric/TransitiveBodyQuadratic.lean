import BanachIsometric.ExactBodyGauge
import BanachIsometric.ExactFamilyModelCoordinates
import BanachIsometric.BodyGroupConjugation

/-! Transitivity of the actual body group on an auxiliary Euclidean unit
sphere makes its definite positive homogeneous gauge a constant times the
Euclidean norm. Pulling back that square gives an actual quadratic form. -/

noncomputable section

namespace BanachIsometric

open Set Metric NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem IsDefinitePositiveHomogeneous.invariant_bodyAutomorphism
    {p : E → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    (a : bodyAutomorphismGroup {x | p x ≤ 1}) (x : E) :
    p ((a.val : E →L[ℝ] E) x) = p x := by
  let A := ContinuousLinearEquiv.ofUnit a.val
  apply gauge_eq_of_exact_body_image hp hp A.toLinearMap A.injective
  change A '' {x | p x ≤ 1} = {x | p x ≤ 1} ∩ Set.range A
  rw [A.surjective.range_eq, inter_univ]
  exact a.property

theorem IsDefinitePositiveHomogeneous.eq_norm_mul_of_transitive_bodyGroup
    {p : E → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    (w : sphere (0 : E) 1)
    (htrans : ∀ u : sphere (0 : E) 1,
      ∃ a : bodyAutomorphismGroup {x | p x ≤ 1},
        (a.val : E →L[ℝ] E) w.val = u.val) :
    ∀ x, p x = p w.val * ‖x‖ := by
  intro x
  by_cases hx : x = 0
  · rw [hx, (hp.eq_zero_iff 0).mpr rfl, norm_zero, mul_zero]
  let u : sphere (0 : E) 1 := ⟨normalize x, by
    simpa only [mem_sphere, dist_zero_right] using norm_normalize hx⟩
  obtain ⟨a, ha⟩ := htrans u
  have hu : p u.val = p w.val := by
    rw [← ha]
    exact hp.invariant_bodyAutomorphism a w.val
  rw [hp.radial_identity hx]
  change ‖x‖ * p u.val = p w.val * ‖x‖
  rw [hu, mul_comm]

theorem exists_posDef_quadraticForm_of_transitive_bodyGroup
    {p : E → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    (w : sphere (0 : E) 1)
    (htrans : ∀ u : sphere (0 : E) 1,
      ∃ a : bodyAutomorphismGroup {x | p x ≤ 1},
        (a.val : E →L[ℝ] E) w.val = u.val) :
    ∃ Q : QuadraticForm ℝ E, Q.PosDef ∧ ∀ x, Q x = p x ^ 2 := by
  let Q : QuadraticForm ℝ E := p w.val ^ 2 •
    LinearMap.BilinMap.toQuadraticMap (innerₗ E)
  have hdiag (x) : Q x = p x ^ 2 := by
    change p w.val ^ 2 * inner ℝ x x = p x ^ 2
    rw [real_inner_self_eq_norm_sq, hp.eq_norm_mul_of_transitive_bodyGroup w htrans x]
    ring
  refine ⟨Q, ?_, hdiag⟩
  intro x hx
  rw [hdiag]
  exact sq_pos_iff.mpr ((hp.eq_zero_iff x).not.mpr hx)

theorem exists_posDef_quadraticForm_of_normalized_transitive_bodyGroup
    {p : E → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    (e : E ≃L[ℝ] E) (w : sphere (0 : E) 1)
    (htrans : ∀ u : sphere (0 : E) 1,
      ∃ a : bodyAutomorphismGroup (e '' {x | p x ≤ 1}),
        (a.val : E →L[ℝ] E) w.val = u.val) :
    ∃ Q : QuadraticForm ℝ E, Q.PosDef ∧ ∀ x, Q x = p x ^ 2 := by
  let q : E → ℝ := fun y => p (e.symm y)
  have hq : IsDefinitePositiveHomogeneous q := hp.comp_continuousLinearEquiv e.symm
  have hbody : e '' {x | p x ≤ 1} = {y | q y ≤ 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change p (e.symm (e x)) ≤ 1
      rw [e.symm_apply_apply]
      exact hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  have htrans' : ∀ u : sphere (0 : E) 1,
      ∃ a : bodyAutomorphismGroup {y | q y ≤ 1},
        (a.val : E →L[ℝ] E) w.val = u.val := by
    rw [hbody] at htrans
    exact htrans
  obtain ⟨Q, _hQpos, hQ⟩ := exists_posDef_quadraticForm_of_transitive_bodyGroup hq w htrans'
  let R := Q.comp e.toLinearMap
  have hR (x) : R x = p x ^ 2 := by
    change Q (e x) = p x ^ 2
    rw [hQ]
    simp only [q, e.symm_apply_apply]
  refine ⟨R, ?_, hR⟩
  intro x hx
  rw [hR]
  exact sq_pos_iff.mpr ((hp.eq_zero_iff x).not.mpr hx)

end BanachIsometric
