import BanachIsometric.SingularPrismGeometry

/-! An explicit natural homeomorphism from the real-coordinate standard
simplex to the nonnegative-real coordinate simplex. The latter is the literal
coordinate model used by Mathlib's topological simplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology NNReal

abbrev NNRealSimplex (n : ℕ) := {w : Fin (n + 1) → ℝ≥0 // ∑ i, w i = 1}

def realNNRealSimplex (n : ℕ) : Simplex n ≃ₜ NNRealSimplex n where
  toFun w := ⟨fun i => ⟨w i, w.property.1 i⟩, by
    apply NNReal.eq
    simpa only [NNReal.coe_sum, NNReal.coe_one] using w.property.2⟩
  invFun w := ⟨fun i => (w.val i : ℝ),
    ⟨fun i => (w.val i).property, by
      have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) w.property
      simpa only [NNReal.coe_sum, NNReal.coe_one] using h⟩⟩
  left_inv w := rfl
  right_inv w := rfl
  continuous_toFun := (continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_pi fun i =>
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _

def nnrealSimplexMap {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) :
    C(NNRealSimplex a, NNRealSimplex b) := by
  let j : C(NNRealSimplex a, stdSimplex ℝ≥0 (Fin (a + 1))) :=
    ⟨fun w => ⟨w.val, (fun _ => zero_le _), w.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let q : C(stdSimplex ℝ≥0 (Fin (b + 1)), NNRealSimplex b) :=
    ⟨fun w => ⟨w.val, w.property.2⟩, continuous_subtype_val.subtype_mk _⟩
  exact q.comp ((⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ :
    C(stdSimplex ℝ≥0 (Fin (a + 1)), stdSimplex ℝ≥0 (Fin (b + 1)))).comp j)

theorem nnrealSimplexMap_apply {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1))
    (w : NNRealSimplex a) (i : Fin (b + 1)) :
    (nnrealSimplexMap f w).val i = ∑ j ∈ Finset.univ.filter (fun j => f j = i), w.val j := by
  exact FunOnFinite.linearMap_apply_apply ℝ≥0 ℝ≥0 f w.val i

theorem realNNRealSimplex_natural {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1))
    (w : Simplex a) :
    realNNRealSimplex b (stdSimplex.map f w) = nnrealSimplexMap f (realNNRealSimplex a w) := by
  apply Subtype.ext
  funext i
  apply NNReal.eq
  change FunOnFinite.linearMap ℝ ℝ f (w : Fin (a + 1) → ℝ) i = _
  rw [FunOnFinite.linearMap_apply_apply, nnrealSimplexMap_apply, NNReal.coe_sum]
  rfl

end BanachIsometric.SingularPrism
