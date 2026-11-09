import BanachIsometric.PulledBackClutching
import Mathlib.SetTheory.Cardinal.Finite

/-! The actual conewise suspension preserves the literal signed height.
Consequently its fiber over an equatorial target is exactly the actual
equator-map fiber. This does not identify their degrees or assert an
orientation sign: the parameter sphere has one higher dimension. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem equatorInclusion_injective (v : sphere (0 : V) 1) :
    Function.Injective (equatorInclusion v) := by
  intro z w he
  exact Subtype.ext (Subtype.ext (congrArg (fun x : sphere (0 : V) 1 => x.val) he))

theorem hemisphereMap_preserves_inner [FiniteDimensional ℝ V]
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v)) (x : closedHemisphere v) :
    inner ℝ v.val (hemisphereMap v q₀ f x).val.val = inner ℝ v.val x.val.val := by
  obtain ⟨⟨t, z⟩, rfl⟩ := hemisphereCone_surjective v q₀ x
  rw [hemisphereMap_cone, hemisphereCone_inner, hemisphereCone_inner]

theorem suspension_preserves_inner [FiniteDimensional ℝ V]
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hN : ∀ x : closedHemisphere v, φ x.val = (hemisphereMap v q₀ f x).val)
    (hS : ∀ x : closedHemisphere (-v), φ x.val =
      (hemisphereMap (-v) (equatorOppositePole v q₀) (oppositeEquatorMap v f) x).val)
    (x : sphere (0 : V) 1) : inner ℝ v.val (φ x).val = inner ℝ v.val x.val := by
  by_cases hx : 0 ≤ inner ℝ v.val x.val
  · have he := hN ⟨x, hx⟩
    change φ x = _ at he
    rw [he]
    exact hemisphereMap_preserves_inner v q₀ f ⟨x, hx⟩
  · have hxS : 0 ≤ inner ℝ (-v.val) x.val := by rw [inner_neg_left]; linarith
    have he := hS ⟨x, hxS⟩
    change φ x = _ at he
    rw [he]
    have h := hemisphereMap_preserves_inner (-v) (equatorOppositePole v q₀)
      (oppositeEquatorMap v f) ⟨x, hxS⟩
    change inner ℝ (-v.val) _ = inner ℝ (-v.val) x.val at h
    rw [inner_neg_left, inner_neg_left] at h
    linarith

def suspensionEquatorialFiberMap
    (v : sphere (0 : V) 1) (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hE : ∀ z, φ (equatorInclusion v z) = equatorInclusion v (f z)) (target : EquatorSphere v) :
    {z : EquatorSphere v // f z = target} →
      {x : sphere (0 : V) 1 // φ x = equatorInclusion v target} := fun z =>
  ⟨equatorInclusion v z.val, (hE z.val).trans (congrArg (equatorInclusion v) z.property)⟩

def suspensionEquatorialFiberEquiv
    (v : sphere (0 : V) 1) (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hheight : ∀ x, inner ℝ v.val (φ x).val = inner ℝ v.val x.val)
    (hE : ∀ z, φ (equatorInclusion v z) = equatorInclusion v (f z)) (target : EquatorSphere v) :
    {z : EquatorSphere v // f z = target} ≃
      {x : sphere (0 : V) 1 // φ x = equatorInclusion v target} :=
  Equiv.ofBijective (suspensionEquatorialFiberMap v f φ hE target) ⟨by
    intro z w he
    apply Subtype.ext
    apply equatorInclusion_injective v
    exact congrArg Subtype.val he,
    by
      intro x
      have hz : inner ℝ v.val x.val.val = 0 := by
        have h := hheight x.val
        rw [x.property, equatorInclusion_inner] at h
        exact h.symm
      let z : EquatorSphere v := ⟨⟨x.val.val,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hz⟩,
        by simpa only [Metric.mem_sphere, dist_zero_right] using norm_eq_of_mem_sphere x.val⟩
      have he : equatorInclusion v z = x.val := by apply Subtype.ext; rfl
      have hfz : f z = target := by
        apply equatorInclusion_injective v
        exact (hE z).symm.trans ((congrArg φ he).trans x.property)
      exact ⟨⟨z, hfz⟩, Subtype.ext he⟩⟩

theorem card_suspension_equatorial_fiber
    (v : sphere (0 : V) 1) (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hheight : ∀ x, inner ℝ v.val (φ x).val = inner ℝ v.val x.val)
    (hE : ∀ z, φ (equatorInclusion v z) = equatorInclusion v (f z)) (target : EquatorSphere v) :
    Nat.card {x : sphere (0 : V) 1 // φ x = equatorInclusion v target} =
      Nat.card {z : EquatorSphere v // f z = target} :=
  (Nat.card_congr (suspensionEquatorialFiberEquiv v f φ hheight hE target)).symm

end BanachIsometric
