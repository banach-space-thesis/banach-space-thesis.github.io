import BanachIsometric.PulledBackClutching
import BanachIsometric.EquatorRepetition
import BanachIsometric.NullClutchingCoreSection

/-! The explicit finite-order clutching reduction. A finite-order class in
the actual connected identity body group yields a positive cubical repetition,
its actual sphere suspension, and a continuous exact operator section over
the pullback. Finiteness/torsion of the even homotopy group, positivity of the
analytic sphere index, and Lipschitz regularization of this sphere map remain
separate obligations. In particular this is not asserted as the full
annihilation theorem of Lemma 4.3. -/

noncomputable section
namespace BanachIsometric
open Set Metric SphereGenerator
open scoped Topology Topology.Homotopy

theorem exists_suspension_exact_section_of_finiteOrder_clutching
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
    ∃ d : ℕ, 0 < d ∧
    ∃ φ : C(sphere (0 : V) 1, sphere (0 : V) 1),
    ∃ out : C(sphere (0 : V) 1, E →L[ℝ] F),
      (∀ z, φ (equatorInclusion v z) =
        equatorInclusion v (e.symm (sphereRepetition n d (e z)))) ∧
      ∀ x, Function.Injective (out x) ∧ LinearMap.range (out x).toLinearMap = H (φ x) ∧
        out x '' S = K ∩ (H (φ x) : Set F) := by
  obtain ⟨d, hd, ⟨hnull⟩⟩ :=
    exists_positive_equatorRepetition_nullhomotopy_of_finiteOrder n e g hg hfin
  let f : C(EquatorSphere v, EquatorSphere v) :=
    (⟨e.symm, e.symm.continuous⟩ : C(Sph (n + 1), EquatorSphere v)).comp
      ((sphereRepetition n d).comp ⟨e, e.continuous⟩)
  let gG := (identityComponentInclusion (bodyAutomorphismGroup S)).comp g
  have hG : ContinuousMap.Homotopy
      (ContinuousMap.const _ (1 : bodyAutomorphismGroup S)) (gG.comp f) :=
    (identityComponentHomotopyToGroup (g.comp f) hnull).cast rfl rfl
  obtain ⟨φ, out, hφ, hout⟩ := exists_suspension_exact_section_of_null_clutching
    v q₀ north south hnorth hsouth gG hglue f hG
  exact ⟨d, hd, φ, out, hφ, hout⟩

end BanachIsometric
