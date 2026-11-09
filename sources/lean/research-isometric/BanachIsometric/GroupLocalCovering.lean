import Mathlib.Topology.Covering
import Mathlib.Topology.Algebra.Group.Basic

/-! A surjective group homomorphism that is a local homeomorphism is an
actual covering map. The evenly covered neighborhoods are constructed from
an actual local inverse, with fiber the actual discrete kernel. -/

noncomputable section
namespace BanachIsometric
open Set Topology

variable {E B : Type*} [Group E] [Group B] [TopologicalSpace E] [TopologicalSpace B]
    [IsTopologicalGroup E] [IsTopologicalGroup B]

omit [IsTopologicalGroup E] [IsTopologicalGroup B] in
theorem discreteTopology_ker_of_isLocalHomeomorph (p : E →* B)
    (hp : IsLocalHomeomorph p) : DiscreteTopology p.ker := by
  haveI : Subsingleton (p '' (p.ker : Set E)) := ⟨by
    intro x y
    apply Subtype.ext
    obtain ⟨a, ha, hax⟩ := x.property
    obtain ⟨b, hb, hby⟩ := y.property
    exact hax.symm.trans ((show p a = 1 from ha).trans
      ((show p b = 1 from hb).symm.trans hby))⟩
  exact hp.isLocalHomeomorphOn.discreteTopology_of_image

def groupFiberSliceHomeomorph (p : E →* B) (hc : Continuous p) {U : Set B} (s : C(U, E))
    (hs : ∀ y, p (s y) = y.val) : p ⁻¹' U ≃ₜ U × p.ker where
  toFun x := (⟨p x.val, x.property⟩, ⟨(s ⟨p x.val, x.property⟩)⁻¹ * x.val, by
    change p ((s ⟨p x.val, x.property⟩)⁻¹ * x.val) = 1
    rw [map_mul, map_inv, hs, inv_mul_cancel]⟩)
  invFun y := ⟨s y.1 * y.2.val, by
    change p (s y.1 * y.2.val) ∈ U
    rw [map_mul, hs, show p y.2.val = 1 from y.2.property, mul_one]
    exact y.1.property⟩
  left_inv x := by
    apply Subtype.ext
    exact mul_inv_cancel_left _ _
  right_inv y := by
    apply Prod.ext
    · apply Subtype.ext
      change p (s y.1 * y.2.val) = y.1.val
      rw [map_mul, hs, show p y.2.val = 1 from y.2.property, mul_one]
    · apply Subtype.ext
      have he : (⟨p (s y.1 * y.2.val), by
          rw [map_mul, hs, show p y.2.val = 1 from y.2.property, mul_one]
          exact y.1.property⟩ : U) = y.1 := by
        apply Subtype.ext
        change p (s y.1 * y.2.val) = y.1.val
        rw [map_mul, hs, show p y.2.val = 1 from y.2.property, mul_one]
      change (s _)⁻¹ * (s y.1 * y.2.val) = y.2.val
      rw [he, inv_mul_cancel_left]
  continuous_toFun := by
    apply Continuous.prodMk
    · exact Continuous.subtype_mk (by fun_prop) _
    · apply Continuous.subtype_mk
      exact (s.continuous.comp (Continuous.subtype_mk (by fun_prop) _)).inv.mul continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (s.continuous.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

omit [IsTopologicalGroup B] in
theorem isCoveringMap_of_surjective_group_localHomeomorph (p : E →* B)
    (hp : IsLocalHomeomorph p) (hsurj : Function.Surjective p) : IsCoveringMap p := by
  letI := discreteTopology_ker_of_isLocalHomeomorph p hp
  intro b
  obtain ⟨e, he⟩ := hsurj b
  obtain ⟨chart, heChart, hpChart⟩ := hp e
  let s : C(chart.target, E) := ⟨fun y => chart.symm y.val,
    chart.continuousOn_invFun.comp_continuous continuous_subtype_val (fun y => y.property)⟩
  have hsection : ∀ y, p (s y) = y.val := by
    intro y
    exact (congrFun hpChart _).trans (chart.right_inv y.property)
  have hcovered : IsEvenlyCovered p b p.ker :=
    ⟨inferInstance, chart.target, by rw [← he, hpChart]; exact chart.map_source heChart,
      chart.open_target, chart.open_target.preimage hp.continuous,
      groupFiberSliceHomeomorph p hp.continuous s hsection, fun _ => rfl⟩
  exact hcovered.to_isEvenlyCovered_preimage

end BanachIsometric
