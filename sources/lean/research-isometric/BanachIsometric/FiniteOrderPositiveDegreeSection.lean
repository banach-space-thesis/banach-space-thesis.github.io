import BanachIsometric.FiniteOrderHomotopicSuspension
import BanachIsometric.EquatorIsometricCoordinates
import BanachIsometric.CloseSphereHomotopy
import BanachIsometric.SphereRepetitionDegree
import BanachIsometric.SuspensionIsometricRegularValueDegree

/-!
# Actual positive-degree pullback section from a finite-order clutching class

One and the same Lipschitz repetition representative supplies both the
literal clutching nullhomotopy and the positive regular fiber computing the
suspension's degree. The equator coordinates retain an actual linear
isometry. Finite order of the specified clutching class is explicit; no
general torsion theorem for compact connected groups is assumed proved.
-/

noncomputable section
namespace BanachIsometric

open Set Metric SphereGenerator
open scoped Topology Topology.Homotopy NNReal

theorem exists_positive_degree_exact_pullback_section_of_finiteOrder
    {V E F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : sphere (0 : V) 1 → Submodule ℝ F}
    {m : ℕ} [NeZero m] (eV : V ≃L[ℝ] PiolaSpace m)
    (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3)
    (north : C(closedHemisphere v, E →L[ℝ] F))
    (south : C(closedHemisphere (-v), E →L[ℝ] F))
    (hnorth : ∀ x, Function.Injective (north x) ∧ LinearMap.range (north x).toLinearMap = H x.val ∧
      north x '' S = K ∩ (H x.val : Set F))
    (hsouth : ∀ x, Function.Injective (south x) ∧ LinearMap.range (south x).toLinearMap = H x.val ∧
      south x '' S = K ∩ (H x.val : Set F))
    (g : C(EquatorSphere v, Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)))
    (hglue : ∀ z, south (equatorSouth v z) = (north (equatorNorth v z)).comp
      (((g z).val).val : E →L[ℝ] E))
    (hg : g ((equatorStandardSphereHomeomorph v (n + 1) hdim).symm
      (sphereBasepoint (n + 1))) = 1)
    (hfin : IsOfFinOrder (genLoopClass (sphereTargetMapGenLoop (n + 1)
      (g.comp ⟨(equatorStandardSphereHomeomorph v (n + 1) hdim).symm,
        (equatorStandardSphereHomeomorph v (n + 1) hdim).symm.continuous⟩) hg))) :
    ∃ d : ℕ, 0 < d ∧ ∃ φ : C(sphere (0 : V) 1, sphere (0 : V) 1),
    ∃ out : C(sphere (0 : V) 1, E →L[ℝ] F), ∃ C : ℝ≥0,
      LipschitzWith C φ ∧ sphereSignedDegree eV φ = (d : ℤ) ∧
      continuousSphereSignedDegree eV φ = (d : ℤ) ∧
      0 < continuousSphereSignedDegree eV φ ∧
      ∀ x, Function.Injective (out x) ∧ LinearMap.range (out x).toLinearMap = H (φ x) ∧
        out x '' S = K ∩ (H (φ x) : Set F) := by
  let L := equatorStandardLinearIsometry v (n + 1) hdim
  let e := equatorStandardSphereHomeomorph v (n + 1) hdim
  let q₀ := e.symm (sphereBasepoint (n + 1))
  obtain ⟨d, hd, hsections⟩ :=
    exists_positive_repeat_exact_for_homotopic_suspensions_of_finiteOrder v q₀
      north south hnorth hsouth g hglue n e hg hfin
  obtain ⟨G, LG, hG, hclose, hreg, hcard⟩ :=
    exists_lipschitz_sphereRepetition_with_positive_anchor n d
  let f := isometricSphereConjugateContinuous L G
  obtain ⟨φ, hN, hS, _⟩ := exists_suspension v q₀ f
  have hBand : ∀ a : Icc (-1 : ℝ) 1, ∀ z, φ (equatorBand v (a, z)) =
      equatorBand v (a, f z) := suspension_equatorBand v q₀ f φ hN hS
  have hSame : f = equatorConjugateSphereMap v n e G := by rfl
  let hHom := closeSphereHomotopy (sphereRepetition n d) G (fun z => by
    rw [dist_comm]
    exact (hclose z).trans (by norm_num))
  obtain ⟨out, hout⟩ := hsections G hHom φ (by simpa only [← hSame] using hBand)
  have hf : LipschitzWith LG f := lipschitzWith_isometricSphereConjugate L hG
  obtain ⟨C, hC⟩ := exists_lipschitz_sphereMap_of_band v q₀ f φ hBand hf
  have hy : ‖sphereRepetitionAnchor n‖ < 1 := by rw [norm_sphereRepetitionAnchor]; norm_num
  have hdegree := sphereSignedDegree_suspension_isometric_eq_natCard eV v q₀ L G φ hBand hG
    (sphereRepetitionAnchor n) hy (fun x _ hx => (hreg x hx).1) (fun x _ hx => (hreg x hx).2)
  rw [hcard] at hdegree
  have hcontinuous : continuousSphereSignedDegree eV φ = (d : ℤ) :=
    (continuousSphereSignedDegree_eq_sphereSignedDegree eV φ hC).trans hdegree
  refine ⟨d, hd, φ, out, C, hC, hdegree, hcontinuous, ?_, hout⟩
  rw [hcontinuous]
  exact_mod_cast hd

end BanachIsometric
