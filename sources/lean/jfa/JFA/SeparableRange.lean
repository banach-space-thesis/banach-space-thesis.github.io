import JFA.Definitions
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Abel

/-! The separable-range operator ideal and scalar-plus-separable uniqueness.
All results in this file are proved for the actual norm topologies. -/

noncomputable section
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem hasSeparableRange_zero : HasSeparableRange 𝕜 E F (0 : E →L[𝕜] F) := by
  change IsSeparable (Set.range (fun _ : E => (0 : F)))
  simpa using (Set.finite_singleton (0 : F)).isSeparable

theorem HasSeparableRange.comp_left {T : E →L[𝕜] F}
    (hT : HasSeparableRange 𝕜 E F T) (A : F →L[𝕜] G) :
    HasSeparableRange 𝕜 E G (A.comp T) := by
  change IsSeparable (Set.range (A ∘ T))
  rw [Set.range_comp]
  exact hT.image A.continuous

theorem HasSeparableRange.comp_right {T : F →L[𝕜] G}
    (hT : HasSeparableRange 𝕜 F G T) (A : E →L[𝕜] F) :
    HasSeparableRange 𝕜 E G (T.comp A) :=
  hT.mono (by rintro _ ⟨x, rfl⟩; exact ⟨A x, rfl⟩)

theorem HasSeparableRange.add {S T : E →L[𝕜] F}
    (hS : HasSeparableRange 𝕜 E F S) (hT : HasSeparableRange 𝕜 E F T) :
    HasSeparableRange 𝕜 E F (S + T) := by
  apply ((hS.prod hT).image (continuous_fst.add continuous_snd)).mono
  rintro _ ⟨x, rfl⟩
  exact ⟨(S x, T x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩

theorem HasSeparableRange.smul {T : E →L[𝕜] F}
    (hT : HasSeparableRange 𝕜 E F T) (a : 𝕜) :
    HasSeparableRange 𝕜 E F (a • T) := by
  apply (hT.image (continuous_const.smul continuous_id : Continuous (fun y : F => a • y))).mono
  rintro _ ⟨x, rfl⟩
  exact ⟨T x, ⟨x, rfl⟩, rfl⟩

theorem HasSeparableRange.neg {T : E →L[𝕜] F}
    (hT : HasSeparableRange 𝕜 E F T) : HasSeparableRange 𝕜 E F (-T) := by
  simpa using hT.smul (-1 : 𝕜)

theorem HasSeparableRange.sub {S T : E →L[𝕜] F}
    (hS : HasSeparableRange 𝕜 E F S) (hT : HasSeparableRange 𝕜 E F T) :
    HasSeparableRange 𝕜 E F (S - T) := by
  simpa [sub_eq_add_neg] using hS.add hT.neg

/-- A nonzero scalar identity cannot have separable range on a nonseparable space. -/
theorem scalar_id_separable_iff (hE : ¬ SeparableSpace E) (a : 𝕜) :
    HasSeparableRange 𝕜 E E (a • ContinuousLinearMap.id 𝕜 E) ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    have hr : Set.range (a • ContinuousLinearMap.id 𝕜 E) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      refine ⟨a⁻¹ • x, ?_⟩
      simp [smul_smul, ha]
    exact hE (isSeparable_univ_iff.mp (hr ▸ h))
  · rintro rfl
    simpa using (hasSeparableRange_zero (𝕜 := 𝕜) (E := E) (F := E))

/-- Uniqueness of the scalar in every scalar-plus-separable decomposition. -/
theorem scalar_decomposition_unique (hE : ¬ SeparableSpace E)
    {T S R : E →L[𝕜] E} {a b : 𝕜}
    (hS : HasSeparableRange 𝕜 E E S) (hR : HasSeparableRange 𝕜 E E R)
    (ha : T = a • ContinuousLinearMap.id 𝕜 E + S)
    (hb : T = b • ContinuousLinearMap.id 𝕜 E + R) : a = b := by
  have hsub : (a - b) • ContinuousLinearMap.id 𝕜 E = R - S := by
    have h : a • ContinuousLinearMap.id 𝕜 E + S =
        b • ContinuousLinearMap.id 𝕜 E + R := ha.symm.trans hb
    rw [sub_smul]
    exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa [add_comm] using h)
  have hz := (scalar_id_separable_iff hE (a - b)).mp (hsub ▸ hR.sub hS)
  exact sub_eq_zero.mp hz

/-- The paper's few-operator hypothesis supplies a unique scalar AND remainder. -/
theorem fewOperators_unique_decomposition (hE : ¬ SeparableSpace E)
    (hfew : HasFewOperators 𝕜 E) (T : E →L[𝕜] E) :
    ∃! d : 𝕜 × (E →L[𝕜] E),
      HasSeparableRange 𝕜 E E d.2 ∧
      T = d.1 • ContinuousLinearMap.id 𝕜 E + d.2 := by
  obtain ⟨a, S, hS, ha⟩ := hfew T
  refine ⟨(a, S), ⟨hS, ha⟩, ?_⟩
  rintro ⟨b, R⟩ ⟨hR, hb⟩
  have hab : b = a := scalar_decomposition_unique hE hR hS hb ha
  subst b
  apply Prod.ext
  · rfl
  · exact add_left_cancel (hb.symm.trans ha)

end JFA
