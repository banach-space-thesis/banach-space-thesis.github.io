import Posets.SupportingStatements

/-! Source discrepancies are recorded as checked counterexamples, never repaired
by silently adding a hypothesis to the paper's target. -/
noncomputable section
open ThesisCommon
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

/-- K=∅ is compact Hausdorff and C(K)=0 is separable. Its operator algebra
has no proper maximal ideal. This refutes the first printed clause of 1.10. -/
theorem proposition_1_10_false_as_printed : ¬ Proposition_1_10_printed 𝕜 := by
  rintro ⟨h, _⟩
  have hbad := h PEmpty (by infer_instance)
  exact not_uniqueMaximal_of_subsingleton 𝕜 hbad

theorem corollary_3_3_false_as_printed : ¬ Corollary_3_3_printed 𝕜 := by
  intro h
  letI : IsEmpty {x : ℝ // False} := ⟨fun x => x.property⟩
  exact not_uniqueMaximal_of_subsingleton 𝕜 (h {x : ℝ // False})

/-- The author-confirmed interpretation; the analytic result remains unproved. -/
abbrev Proposition_1_10_nonempty := Proposition_1_10 𝕜

end Posets
