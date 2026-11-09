import BanachIsometric.SphereRepetitionGermSet
import BanachIsometric.SphereFiberGermApproximation
import BanachIsometric.SphereConeGerms
import BanachIsometric.UnitSphereConeFibers

/-! A genuine global Lipschitz representative retains the exact chosen
repetition fiber and all its positive derivative germs. -/

namespace BanachIsometric.SphereGenerator

open Set Metric NormedSpace Filter
open scoped Topology NNReal

noncomputable section

def sphereRepetitionAnchor (n : ℕ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (1 / 2 : ℝ) • (axisSphereTarget n).val

theorem norm_sphereRepetitionAnchor (n : ℕ) : ‖sphereRepetitionAnchor n‖ = 1 / 2 := by
  have hn : ‖(axisSphereTarget n).val‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (axisSphereTarget n).property
  simp [sphereRepetitionAnchor, norm_smul, hn]

theorem sphereRepetitionAnchor_ne_zero (n : ℕ) : sphereRepetitionAnchor n ≠ 0 := by
  intro he
  have hn := norm_sphereRepetitionAnchor n
  rw [he, norm_zero] at hn
  norm_num at hn

theorem coneDirection_sphereRepetitionAnchor (n : ℕ) :
    coneDirection (sphereRepetitionAnchor n) (sphereRepetitionAnchor_ne_zero n) = axisSphereTarget n := by
  apply Subtype.ext
  change normalize ((1 / 2 : ℝ) • (axisSphereTarget n).val) = (axisSphereTarget n).val
  rw [normalize_smul_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  apply normalize_eq_self_of_norm_eq_one
  simpa only [mem_sphere, dist_zero_right] using (axisSphereTarget n).property

theorem positive_anchor_of_preserved_repetition_germs (n d : ℕ)
    (hraw : ∀ w : Sph (n + 1), sphereRepetition n d w = axisSphereTarget n →
      DifferentiableAt ℝ (unitSphereCone (sphereRepetition n d)) ((1 / 2 : ℝ) • w.val) ∧
      0 < (fderiv ℝ (unitSphereCone (sphereRepetition n d)) ((1 / 2 : ℝ) • w.val)).det)
    (G : Sph (n + 1) → Sph (n + 1))
    (hfiber : ∀ w, G w = axisSphereTarget n ↔ sphereRepetition n d w = axisSphereTarget n)
    (hgerm : ∀ w, sphereRepetition n d w = axisSphereTarget n → G =ᶠ[𝓝 w] sphereRepetition n d)
    (x : EuclideanSpace ℝ (Fin (n + 2)))
    (hx : unitSphereCone G x = sphereRepetitionAnchor n) :
    DifferentiableAt ℝ (unitSphereCone G) x ∧
      0 < (fderiv ℝ (unitSphereCone G) x).det := by
  have hxne := unitSphereCone_preimage_ne_zero G (sphereRepetitionAnchor_ne_zero n) hx
  let w := coneDirection x hxne
  have hnorm : ‖x‖ = 1 / 2 := by
    rw [← norm_unitSphereCone G x, hx, norm_sphereRepetitionAnchor]
  have hrepr : x = (1 / 2 : ℝ) • w.val := by
    change x = (1 / 2 : ℝ) • normalize x
    rw [← hnorm, norm_smul_normalize]
  have hwG : G w = axisSphereTarget n := by
    apply Subtype.ext
    have he := congrArg NormedSpace.normalize hx
    rw [normalize_unitSphereCone G x hxne] at he
    exact he.trans (congrArg Subtype.val (coneDirection_sphereRepetitionAnchor n))
  have hw := (hfiber w).mp hwG
  have hraw := hraw w hw
  have heq := unitSphereCone_eventuallyEq_of_sphere_germ (hgerm w hw) (by norm_num : (0 : ℝ) < 1 / 2)
  have hG := hraw.1.hasFDerivAt.congr_of_eventuallyEq heq
  rw [hrepr]
  refine ⟨hG.differentiableAt, ?_⟩
  rw [hG.fderiv]
  exact hraw.2

theorem exists_lipschitz_sphereRepetition_with_positive_anchor_of_positive_raw_germs (n d : ℕ)
    (hraw : ∀ w : Sph (n + 1), sphereRepetition n d w = axisSphereTarget n →
      DifferentiableAt ℝ (unitSphereCone (sphereRepetition n d)) ((1 / 2 : ℝ) • w.val) ∧
      0 < (fderiv ℝ (unitSphereCone (sphereRepetition n d)) ((1 / 2 : ℝ) • w.val)).det) :
    ∃ G : C(Sph (n + 1), Sph (n + 1)), ∃ L : ℝ≥0, LipschitzWith L G ∧
      (∀ w, dist (G w) (sphereRepetition n d w) < (1 / 4 : ℝ)) ∧
      (∀ x, unitSphereCone G x = sphereRepetitionAnchor n →
        DifferentiableAt ℝ (unitSphereCone G) x ∧ 0 < (fderiv ℝ (unitSphereCone G) x).det) ∧
      Nat.card {x : EuclideanSpace ℝ (Fin (n + 2)) //
        x ∈ closedBall 0 1 ∧ unitSphereCone G x = sphereRepetitionAnchor n} = d := by
  obtain ⟨A, hAc, hAf, K, hK⟩ :=
    exists_compact_lipschitzOn_sphereRepetition_fiber_neighborhood n d
      (axisSphereTarget n) (axisSphereTarget_ne_basepoint n)
  obtain ⟨G, L, hL, hclose, hfiber, hgerm⟩ :=
    exists_lipschitz_sphere_approximation_preserving_fiber_germs (sphereRepetition n d)
      (axisSphereTarget n) hAc hK hAf (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨G, L, hL, hclose, positive_anchor_of_preserved_repetition_germs n d hraw G hfiber hgerm, ?_⟩
  have hcard := card_unitSphereCone_fiber G (sphereRepetitionAnchor n)
    (sphereRepetitionAnchor_ne_zero n) (by rw [norm_sphereRepetitionAnchor]; norm_num)
  rw [coneDirection_sphereRepetitionAnchor] at hcard
  let e : {w : Sph (n + 1) // G w = axisSphereTarget n} ≃
      {w : Sph (n + 1) // sphereRepetition n d w = axisSphereTarget n} :=
    { toFun := fun w => ⟨w.val, (hfiber w.val).mp w.property⟩
      invFun := fun w => ⟨w.val, (hfiber w.val).mpr w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact hcard.trans ((Nat.card_congr e).trans
    (card_sphereRepetition_fiber n d (axisSphereTarget n) (axisSphereTarget_ne_basepoint n)))

end
end BanachIsometric.SphereGenerator
