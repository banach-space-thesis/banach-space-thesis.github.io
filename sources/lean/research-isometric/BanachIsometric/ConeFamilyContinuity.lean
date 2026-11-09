import BanachIsometric.LipschitzCone

/-!
# Joint continuity of actual cone families off the vertex

Boundary homotopy invariance only needs joint continuity on the source
boundary. The formula is proved continuous on the actual punctured ambient
space, then restricted to any boundary which avoids the origin.
-/

namespace BanachIsometric

open NormedSpace Set

variable {P V W : Type*} [TopologicalSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem continuous_coneDirection_punctured :
    Continuous (fun x : {x : V // x ≠ 0} => coneDirection x.val x.property) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul
    continuous_subtype_val

theorem continuous_coneExtension_family_punctured
    (H : P → Metric.sphere (0 : V) 1 → W)
    (hH : Continuous (fun z : P × Metric.sphere (0 : V) 1 => H z.1 z.2)) :
    Continuous (fun z : P × {x : V // x ≠ 0} => coneExtension (H z.1) z.2.val) := by
  have he : (fun z : P × {x : V // x ≠ 0} => coneExtension (H z.1) z.2.val) =
      (fun z => ‖z.2.val‖ • H z.1 (coneDirection z.2.val z.2.property)) := by
    funext z
    exact coneExtension_of_ne _ _ z.2.property
  rw [he]
  exact (continuous_subtype_val.comp continuous_snd).norm.smul
    (hH.comp (continuous_fst.prodMk (continuous_coneDirection_punctured.comp continuous_snd)))

theorem continuous_coneExtension_family_on_subset
    (H : P → Metric.sphere (0 : V) 1 → W)
    (hH : Continuous (fun z : P × Metric.sphere (0 : V) 1 => H z.1 z.2))
    (b : Set V) (hb : ∀ x ∈ b, x ≠ 0) :
    Continuous (fun z : P × b => coneExtension (H z.1) z.2.val) := by
  let inc : P × b → P × {x : V // x ≠ 0} := fun z =>
    (z.1, ⟨z.2.val, hb z.2.val z.2.property⟩)
  have hi : Continuous inc := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  exact (continuous_coneExtension_family_punctured H hH).comp hi

end BanachIsometric
