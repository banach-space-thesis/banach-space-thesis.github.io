import ThesisCommon.Analysis.Cotype

/-! Cotype passes through an additive norm-preserving embedding, with no
change of either exponent or constant. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]

theorem HasRademacherCotype.of_norm_preserving_addHom {q C : ℝ}
    (h : HasRademacherCotype Y q C) (e : X →+ Y) (he : ∀ x, ‖e x‖ = ‖x‖) :
    HasRademacherCotype X q C := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro n x
  have hsum (θ : Fin n → Bool) :
      (∑ i, if θ i then e (x i) else -e (x i)) =
      e (∑ i, if θ i then x i else -x i) := by
    simp only [map_sum, apply_ite, map_neg]
  have hx := h.2.2 n (fun i => e (x i))
  simpa only [hsum, he] using hx

theorem HasFiniteCotype.of_norm_preserving_addHom
    (h : HasFiniteCotype Y) (e : X →+ Y) (he : ∀ x, ‖e x‖ = ‖x‖) :
    HasFiniteCotype X := by
  obtain ⟨q, C, h⟩ := h
  exact ⟨q, C, h.of_norm_preserving_addHom e he⟩

end ThesisCommon
