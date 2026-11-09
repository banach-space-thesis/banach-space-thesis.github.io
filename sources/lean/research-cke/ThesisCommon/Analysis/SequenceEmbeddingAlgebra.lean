import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.CZeroOperators

/-! Composition and monotonicity of coordinate insertions.
The range-containment bridge transfers small operator restrictions to subsets.
-/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {ι κ ν : Type*}

/-- Enumeration of the strictly later coordinates of an injective sequence. -/
def coordinateTail (e : ℕ ↪ ℕ) (k : ℕ) : ℕ ↪ ℕ where
  toFun j := e (k + 1 + j)
  inj' := by intro i j h; have := e.injective h; omega

/-- An injection whose range is contained in another factors through it. -/
theorem exists_embedding_factor (e : κ ↪ ν) (f : ι ↪ ν)
    (h : Set.range f ⊆ Set.range e) : ∃ g : ι ↪ κ, g.trans e = f := by
  classical
  have hf : ∀ i, ∃ j, e j = f i := fun i => h ⟨i, rfl⟩
  choose g hg using hf
  refine ⟨⟨g, ?_⟩, ?_⟩
  · intro i j hij
    apply f.injective
    rw [← hg i, ← hg j, hij]
  · ext i
    exact hg i

/-- Zero insertion along composed injections equals composition of insertions. -/
theorem lpExtend_comp {p : ℝ≥0∞} [Fact (1 ≤ p)] (e : ι ↪ κ) (f : κ ↪ ν) :
    (lpExtend (𝕜 := 𝕜) (X := X) p f).comp (lpExtend p e) = lpExtend p (e.trans f) := by
  ext x k
  change Function.extend f (Function.extend e x 0) 0 k = Function.extend (f ∘ e) x 0 k
  exact congrFun (e.injective.extend_comp f.injective x 0).symm k

/-- Passing to a smaller coordinate set cannot increase a restricted norm. -/
theorem norm_comp_lpExtend_le_of_range_subset {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : lp (fun _ : ν => X) p →L[𝕜] Y) (e : κ ↪ ν) (f : ι ↪ ν)
    (h : Set.range f ⊆ Set.range e) :
    ‖T.comp (lpExtend p f)‖ ≤ ‖T.comp (lpExtend p e)‖ := by
  obtain ⟨g, rfl⟩ := exists_embedding_factor e f h
  rw [← lpExtend_comp, ← ContinuousLinearMap.comp_assoc]
  calc
    _ ≤ ‖T.comp (lpExtend p e)‖ * ‖lpExtend (𝕜 := 𝕜) (X := X) p g‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T.comp (lpExtend p e)‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_lpExtend_le g) (norm_nonneg _)
    _ = _ := mul_one _

variable [TopologicalSpace ι] [DiscreteTopology ι]
variable [TopologicalSpace κ] [DiscreteTopology κ]
variable [TopologicalSpace ν] [DiscreteTopology ν]

/-- Composition of zero insertions for actual null families. -/
theorem cZeroExtend_comp (e : ι ↪ κ) (f : κ ↪ ν) :
    (cZeroExtend (𝕜 := 𝕜) (X := X) f).comp (cZeroExtend e) = cZeroExtend (e.trans f) := by
  ext x k
  change Function.extend f (Function.extend e x 0) 0 k = Function.extend (f ∘ e) x 0 k
  exact congrFun (e.injective.extend_comp f.injective x 0).symm k

/-- Restricting a c₀ operator to fewer coordinates decreases its norm. -/
theorem norm_comp_cZeroExtend_le_of_range_subset
    (T : C₀(ν, X) →L[𝕜] Y) (e : κ ↪ ν) (f : ι ↪ ν)
    (h : Set.range f ⊆ Set.range e) :
    ‖T.comp (cZeroExtend f)‖ ≤ ‖T.comp (cZeroExtend e)‖ := by
  obtain ⟨g, rfl⟩ := exists_embedding_factor e f h
  rw [← cZeroExtend_comp, ← ContinuousLinearMap.comp_assoc]
  calc
    _ ≤ ‖T.comp (cZeroExtend e)‖ * ‖cZeroExtend (𝕜 := 𝕜) (X := X) g‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T.comp (cZeroExtend e)‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_cZeroExtend_le g) (norm_nonneg (T.comp (cZeroExtend e)))
    _ = _ := mul_one _

end ThesisCommon
