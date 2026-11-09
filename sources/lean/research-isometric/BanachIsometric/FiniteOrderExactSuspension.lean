import BanachIsometric.SuppliedSuspensionClutching
import BanachIsometric.SuspensionRepetitionFibers
import BanachIsometric.EquatorRepetition
import BanachIsometric.NullClutchingCoreSection

/-! A single actual suspension simultaneously has the explicit repetition
band action, the correct literal fibers, and a continuous exact pullback
operator section, provided the specified actual connected-group clutching
class has finite order. This condition is explicit and has not been proved
for arbitrary compact connected matrix groups in this project. Likewise no
sphere-degree equality is included as an assumption or asserted here. -/

noncomputable section
namespace BanachIsometric
open Set Metric SphereGenerator
open scoped Topology Topology.Homotopy

theorem exists_exact_suspension_of_finiteOrder_clutching
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
    ∃ d : ℕ, 0 < d ∧ ∃ φ : C(sphere (0 : V) 1, sphere (0 : V) 1),
    ∃ out : C(sphere (0 : V) 1, E →L[ℝ] F),
      (∀ x, inner ℝ v.val (φ x).val = inner ℝ v.val x.val) ∧
      (∀ a : Icc (-1 : ℝ) 1, ∀ z, φ (equatorBand v (a, z)) =
        equatorBand v (a, equatorSphereRepetition v n d e z)) ∧
      (∀ x, Function.Injective (out x) ∧ LinearMap.range (out x).toLinearMap = H (φ x) ∧
        out x '' S = K ∩ (H (φ x) : Set F)) ∧
      ∀ t : Sph (n + 1), t ≠ sphereBasepoint (n + 1) →
        Finite {x : sphere (0 : V) 1 // φ x = equatorInclusion v (e.symm t)} ∧
        Nat.card {x : sphere (0 : V) 1 // φ x = equatorInclusion v (e.symm t)} = d := by
  obtain ⟨d, hd, ⟨hnull⟩⟩ :=
    exists_positive_equatorRepetition_nullhomotopy_of_finiteOrder n e g hg hfin
  let f := equatorSphereRepetition v n d e
  obtain ⟨φ, hheight, _, hband, hfibers⟩ := exists_suspension_repetition_with_finite_fibers v q₀ n d e
  let gG := (identityComponentInclusion (bodyAutomorphismGroup S)).comp g
  have hG : ContinuousMap.Homotopy
      (ContinuousMap.const _ (1 : bodyAutomorphismGroup S)) (gG.comp f) :=
    (identityComponentHomotopyToGroup (g.comp f) hnull).cast rfl rfl
  obtain ⟨out, hout⟩ := exists_exact_section_for_supplied_suspension_of_null_clutching
    v q₀ north south hnorth hsouth gG hglue f φ hband hG
  exact ⟨d, hd, φ, out, hheight, hband, hout, hfibers⟩

end BanachIsometric
