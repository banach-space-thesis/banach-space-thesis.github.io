import BanachIsometric.SuspensionBand
import BanachIsometric.SphereRepetitionFibers

/-! An actual suspension on the one-higher parameter sphere, with signed
height preserved, exact equatorial-band action, and literal finite fibers of
cardinality `d` over the specified equatorial targets. No equality of degrees
between the equator map and its suspension is assumed or claimed. -/

noncomputable section
namespace BanachIsometric
open Set Metric SphereGenerator
open scoped Topology

def conjugateSelfMapFiberEquiv {Q R : Type*} (e : Q ≃ R) (f : R → R) (t : R) :
    {q : Q // e.symm (f (e q)) = e.symm t} ≃ {r : R // f r = t} where
  toFun q := ⟨e q.val, by
    have h := congrArg e q.property
    simpa only [Equiv.apply_symm_apply] using h⟩
  invFun r := ⟨e.symm r.val, by
    rw [e.apply_symm_apply, r.property]⟩
  left_inv q := by apply Subtype.ext; exact e.symm_apply_apply q.val
  right_inv r := by apply Subtype.ext; exact e.apply_symm_apply r.val

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def equatorSphereRepetition (v : sphere (0 : V) 1) (n d : ℕ)
    (e : EquatorSphere v ≃ₜ Sph (n + 1)) : C(EquatorSphere v, EquatorSphere v) :=
  (⟨e.symm, e.symm.continuous⟩ : C(Sph (n + 1), EquatorSphere v)).comp
    ((sphereRepetition n d).comp ⟨e, e.continuous⟩)

theorem exists_suspension_repetition_with_finite_fibers [FiniteDimensional ℝ V]
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v) (n d : ℕ)
    (e : EquatorSphere v ≃ₜ Sph (n + 1)) :
    ∃ φ : C(sphere (0 : V) 1, sphere (0 : V) 1),
      (∀ x, inner ℝ v.val (φ x).val = inner ℝ v.val x.val) ∧
      (∀ z, φ (equatorInclusion v z) = equatorInclusion v (equatorSphereRepetition v n d e z)) ∧
      (∀ a : Icc (-1 : ℝ) 1, ∀ z, φ (equatorBand v (a, z)) =
        equatorBand v (a, equatorSphereRepetition v n d e z)) ∧
      ∀ t : Sph (n + 1), t ≠ sphereBasepoint (n + 1) →
        Finite {x : sphere (0 : V) 1 // φ x = equatorInclusion v (e.symm t)} ∧
        Nat.card {x : sphere (0 : V) 1 // φ x = equatorInclusion v (e.symm t)} = d := by
  let f := equatorSphereRepetition v n d e
  obtain ⟨φ, hN, hS, hE⟩ := exists_suspension v q₀ f
  have hheight := suspension_preserves_inner v q₀ f φ hN hS
  refine ⟨φ, hheight, hE, suspension_equatorBand v q₀ f φ hN hS, ?_⟩
  intro t ht
  letI := finite_sphereRepetition_fiber n d t ht
  let ec := conjugateSelfMapFiberEquiv e.toEquiv (sphereRepetition n d) t
  letI : Finite {z : EquatorSphere v // f z = e.symm t} := Finite.of_equiv _ ec.symm
  have heq := suspensionEquatorialFiberEquiv v f φ hheight hE (e.symm t)
  refine ⟨Finite.of_equiv _ heq, ?_⟩
  rw [← Nat.card_congr heq]
  exact (Nat.card_congr ec).trans (card_sphereRepetition_fiber n d t ht)

end BanachIsometric
