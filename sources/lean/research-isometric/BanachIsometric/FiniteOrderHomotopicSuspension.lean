import BanachIsometric.ClutchingHomotopyTransfer
import BanachIsometric.EquatorRepetition
import BanachIsometric.NullClutchingCoreSection

/-! Finite-order actual clutching gives a positive repetition number whose
EVERY actual homotopic equator representative has exact operators for any
supplied suspension with that representative's literal band action. In
particular an actual Lipschitz approximation with an actual homotopy can be
used without assuming homotopy invariance of bundle classification.

The compact-connected-group torsion theorem is not asserted: finite order of
the specified actual clutching class remains an explicit premise. -/

noncomputable section
namespace BanachIsometric
open Set Metric SphereGenerator
open scoped Topology Topology.Homotopy

def equatorConjugateSphereMap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : sphere (0 : V) 1) (n : ℕ) (e : EquatorSphere v ≃ₜ Sph (n + 1))
    (G : C(Sph (n + 1), Sph (n + 1))) : C(EquatorSphere v, EquatorSphere v) :=
  (⟨e.symm, e.symm.continuous⟩ : C(Sph (n + 1), EquatorSphere v)).comp
    (G.comp ⟨e, e.continuous⟩)

theorem exists_positive_repeat_exact_for_homotopic_suspensions_of_finiteOrder
    {V E F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : sphere (0 : V) 1 → Submodule ℝ F}
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (north : C(closedHemisphere v, E →L[ℝ] F))
    (south : C(closedHemisphere (-v), E →L[ℝ] F))
    (hnorth : ∀ x, Function.Injective (north x) ∧ LinearMap.range (north x).toLinearMap = H x.val ∧
      north x '' S = K ∩ (H x.val : Set F))
    (hsouth : ∀ x, Function.Injective (south x) ∧ LinearMap.range (south x).toLinearMap = H x.val ∧
      south x '' S = K ∩ (H x.val : Set F))
    (g : C(EquatorSphere v, Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)))
    (hglue : ∀ z, south (equatorSouth v z) = (north (equatorNorth v z)).comp
      (((g z).val).val : E →L[ℝ] E))
    (n : ℕ) (e : EquatorSphere v ≃ₜ Sph (n + 1))
    (hg : g (e.symm (sphereBasepoint (n + 1))) = 1)
    (hfin : IsOfFinOrder (genLoopClass (sphereTargetMapGenLoop (n + 1)
      (g.comp ⟨e.symm, e.symm.continuous⟩) hg))) :
    ∃ d : ℕ, 0 < d ∧ ∀ G : C(Sph (n + 1), Sph (n + 1)),
      ContinuousMap.Homotopy (sphereRepetition n d) G →
      ∀ φ : C(sphere (0 : V) 1, sphere (0 : V) 1),
      (∀ a : Icc (-1 : ℝ) 1, ∀ z, φ (equatorBand v (a, z)) =
        equatorBand v (a, equatorConjugateSphereMap v n e G z)) →
      ∃ out : C(sphere (0 : V) 1, E →L[ℝ] F),
        ∀ x, Function.Injective (out x) ∧ LinearMap.range (out x).toLinearMap = H (φ x) ∧
          out x '' S = K ∩ (H (φ x) : Set F) := by
  obtain ⟨d, hd, ⟨hnull⟩⟩ :=
    exists_positive_equatorRepetition_nullhomotopy_of_finiteOrder n e g hg hfin
  refine ⟨d, hd, ?_⟩
  intro G hG φ hband
  let f₁ := equatorConjugateSphereMap v n e G
  let hEquator := conjugateSphereHomotopy e hG
  let hNull₁ := nullClutchingHomotopyTransfer g hnull hEquator
  let gBody := (identityComponentInclusion (bodyAutomorphismGroup S)).comp g
  have hNullBody : ContinuousMap.Homotopy
      (ContinuousMap.const _ (1 : bodyAutomorphismGroup S)) (gBody.comp f₁) :=
    (identityComponentHomotopyToGroup (g.comp f₁) hNull₁).cast rfl rfl
  exact exists_exact_section_for_supplied_suspension_of_null_clutching
    v q₀ north south hnorth hsouth gBody hglue f₁ φ hband hNullBody

end BanachIsometric
