import ThesisCommon.Analysis.StrictlySingularFiniteRank

/-! Closedness of the genuine set of strictly singular operators. This is
the closedness clause needed for its eventual ideal quotient; closure under
addition and the representation theorem are separate obligations. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem isClosed_strictlySingularOperators :
    IsClosed {T : X →L[𝕜] X | IsStrictlySingularOperator T} := by
  apply isClosed_of_closure_subset
  intro T hT E hE
  obtain ⟨c, hc, hb⟩ := hE
  obtain ⟨S, hS, hST⟩ := Metric.mem_closure_iff.mp hT (c / 2) (by positivity)
  apply hS E
  refine ⟨c / 2, by positivity, ?_⟩
  intro x
  have hn : ‖T - S‖ ≤ c / 2 := by
    simpa only [dist_eq_norm] using hST.le
  have herr : ‖T x.val - S x.val‖ ≤ c / 2 * ‖x‖ := by
    simpa only [ContinuousLinearMap.sub_apply, Submodule.norm_coe] using
      (T - S).le_of_opNorm_le hn x.val
  have ht := hb x
  have htri : ‖T x.val‖ ≤ ‖T x.val - S x.val‖ + ‖S x.val‖ := by
    simpa only [add_comm] using norm_le_insert' (T x.val) (S x.val)
  linarith

end ThesisCommon
