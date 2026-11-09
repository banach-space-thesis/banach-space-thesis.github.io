import BanachIsometric.HemisphereSuspension
import BanachIsometric.ClutchingTrivialization

/-! A nullhomotopy of the actual equatorial pullback produces an actual
global exact operator family over the suspension pullback. This is the
concrete clutching direction needed in Lemma 4.3; no classification of
bundles or identification of homotopy classes is assumed. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def oppositeEquatorMap (v : sphere (0 : V) 1) (f : C(EquatorSphere v, EquatorSphere v)) :
    C(EquatorSphere (-v), EquatorSphere (-v)) :=
  (⟨equatorOppositePole v, (equatorOppositePole v).continuous⟩ :
    C(EquatorSphere v, EquatorSphere (-v))).comp
      (f.comp ⟨(equatorOppositePole v).symm, (equatorOppositePole v).symm.continuous⟩)

theorem hemisphereMap_south_equator [FiniteDimensional ℝ V] (v : sphere (0 : V) 1)
    (q₀ : EquatorSphere v) (f : C(EquatorSphere v, EquatorSphere v)) (z : EquatorSphere v) :
    hemisphereMap (-v) (equatorOppositePole v q₀) (oppositeEquatorMap v f)
      (equatorSouth v z) = equatorSouth v (f z) := by
  have hs : equatorSouth v z = equatorNorth (-v) (equatorOppositePole v z) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hs, hemisphereMap_equator]
  apply Subtype.ext
  apply Subtype.ext
  change (f ((equatorOppositePole v).symm (equatorOppositePole v z))).val.val = (f z).val.val
  rw [Homeomorph.symm_apply_apply]

theorem exists_suspension_exact_section_of_null_clutching
    [FiniteDimensional ℝ V]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : sphere (0 : V) 1 → Submodule ℝ F}
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (north : C(closedHemisphere v, E →L[ℝ] F))
    (south : C(closedHemisphere (-v), E →L[ℝ] F))
    (hnorth : ∀ x, Function.Injective (north x) ∧ LinearMap.range (north x).toLinearMap = H x.val ∧
      north x '' S = K ∩ (H x.val : Set F))
    (hsouth : ∀ x, Function.Injective (south x) ∧ LinearMap.range (south x).toLinearMap = H x.val ∧
      south x '' S = K ∩ (H x.val : Set F))
    (g : C(EquatorSphere v, bodyAutomorphismGroup S))
    (hglue : ∀ z, south (equatorSouth v z) = (north (equatorNorth v z)).comp
      ((g z).val : E →L[ℝ] E))
    (f : C(EquatorSphere v, EquatorSphere v))
    (hnull : ContinuousMap.Homotopy
      (ContinuousMap.const _ (1 : bodyAutomorphismGroup S)) (g.comp f)) :
    ∃ φ : C(sphere (0 : V) 1, sphere (0 : V) 1),
    ∃ out : C(sphere (0 : V) 1, E →L[ℝ] F),
      (∀ z, φ (equatorInclusion v z) = equatorInclusion v (f z)) ∧
      ∀ x, Function.Injective (out x) ∧ LinearMap.range (out x).toLinearMap = H (φ x) ∧
        out x '' S = K ∩ (H (φ x) : Set F) := by
  obtain ⟨φ, hφN, hφS, hφE⟩ := exists_suspension v q₀ f
  let N := hemisphereMap v q₀ f
  let T := hemisphereMap (-v) (equatorOppositePole v q₀) (oppositeEquatorMap v f)
  let north' := north.comp N
  let south' := south.comp T
  have hnorth' : ∀ x, Function.Injective (north' x) ∧
      LinearMap.range (north' x).toLinearMap = H (φ x.val) ∧
      north' x '' S = K ∩ (H (φ x.val) : Set F) := by
    intro x
    rw [hφN x]
    exact hnorth (N x)
  have hsouth' : ∀ x, Function.Injective (south' x) ∧
      LinearMap.range (south' x).toLinearMap = H (φ x.val) ∧
      south' x '' S = K ∩ (H (φ x.val) : Set F) := by
    intro x
    rw [hφS x]
    exact hsouth (T x)
  have hglue' : ∀ z, south' (equatorSouth v z) = (north' (equatorNorth v z)).comp
      (((g.comp f) z).val : E →L[ℝ] E) := by
    intro z
    change south (T (equatorSouth v z)) = (north (N (equatorNorth v z))).comp
      ((g (f z)).val : E →L[ℝ] E)
    dsimp only [T, N]
    rw [hemisphereMap_south_equator, hemisphereMap_equator]
    exact hglue (f z)
  obtain ⟨out, hout⟩ := exists_global_exact_section_of_null_clutching
    (H := fun x => H (φ x)) v q₀ north' south' hnorth' hsouth' (g.comp f) hglue' hnull
  exact ⟨φ, out, hφE, hout⟩

end BanachIsometric
