import BanachIsometric.PolynomialQuadratic
import BanachIsometric.CoordinateOrthogonality
import BanachIsometric.StarBody

/-!
# Polynomial-square extraction on the genuine Euclidean model

The coordinate polynomial argument produces a quadratic form on the original
Euclidean model through an explicit real linear equivalence. The Pi-coordinate
norm is never replaced by an inner-product norm.
-/

namespace BanachIsometric

theorem exists_posDef_euclidean_quadraticForm_of_consecutive_even_powers
    {m a : ℕ} {p : EuclideanSpace ℝ (Fin m) → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (ha : 0 < a)
    (hP : ∃ P : MvPolynomial (Fin m) ℝ, ∀ y : EuclideanSpace ℝ (Fin m),
      MvPolynomial.eval (fun j => y j) P = p y ^ (2 * a))
    (hQ : ∃ Q : MvPolynomial (Fin m) ℝ, ∀ y : EuclideanSpace ℝ (Fin m),
      MvPolynomial.eval (fun j => y j) Q = p y ^ (2 * a + 2)) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧
      ∀ y, Q y = p y ^ 2 := by
  let e := euclideanCoordinates m
  let p' : (Fin m → ℝ) → ℝ := fun x => p (e.symm x)
  have hscale : ∀ x : Fin m → ℝ, p' (fun i => (2 : ℝ) * x i) = 2 * p' x := by
    intro x
    change p (e.symm ((2 : ℝ) • x)) = 2 * p (e.symm x)
    rw [map_smul, hp.smul_nonneg 2 (by norm_num)]
  have hpos : ∀ x : Fin m → ℝ, x ≠ 0 → 0 < p' x := by
    intro x hx
    apply hp.pos
    intro hz
    apply hx
    have he := congrArg e hz
    simpa only [e.apply_symm_apply, map_zero] using he
  have hP' : IsPolynomialFunction (fun x => p' x ^ (2 * a)) := by
    obtain ⟨P, hP⟩ := hP
    refine ⟨P, fun x => ?_⟩
    have hv := hP (e.symm x)
    change MvPolynomial.eval (e (e.symm x)) P = p' x ^ (2 * a) at hv
    simpa only [e.apply_symm_apply] using hv
  have hQ' : IsPolynomialFunction (fun x => p' x ^ (2 * a + 2)) := by
    obtain ⟨Q, hQ⟩ := hQ
    refine ⟨Q, fun x => ?_⟩
    have hv := hQ (e.symm x)
    change MvPolynomial.eval (e (e.symm x)) Q = p' x ^ (2 * a + 2) at hv
    simpa only [e.apply_symm_apply] using hv
  obtain ⟨Q, hQpos, hQval⟩ :=
    exists_posDef_quadraticForm_of_consecutive_even_powers ha hscale hpos hP' hQ'
  refine ⟨Q.comp e.toLinearMap, ?_, ?_⟩
  · intro y hy
    apply hQpos
    intro hz
    exact hy (e.injective (hz.trans (map_zero e).symm))
  · intro y
    change Q (e y) = p y ^ 2
    simpa only [p', e.symm_apply_apply] using hQval (e y)

end BanachIsometric
