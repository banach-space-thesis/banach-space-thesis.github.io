import ThesisCommon.Analysis.UniformPrimariness
import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Analysis.Normed.Lp.ProdLp

/-! Concrete objects and numerical bounds for quantitative decomposition.
Complementation is expressed by an actual bounded retraction onto a closed
submodule. The finite direct sum has its genuine mathlib ℓp product norm.
No decomposition or isomorphism conclusion is included in these definitions.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type u) (Y : Type v)
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- X contains a complemented subspace isomorphic to Y. The retraction has
the inherited subspace norm; its composite with inclusion is a projection. -/
def HasComplementedCopy : Prop :=
  ∃ E : Submodule 𝕜 X, IsClosed (E : Set X) ∧
    ∃ P : X →L[𝕜] E, (∀ x : E, P (x : X) = x) ∧ Nonempty (Y ≃L[𝕜] E)

/-- Compatibility with mathlib's existing complemented-submodule predicate. -/
theorem hasComplementedCopy_iff_exists_closedComplemented :
    HasComplementedCopy 𝕜 X Y ↔
      ∃ E : Submodule 𝕜 X, E.ClosedComplemented ∧ Nonempty (Y ≃L[𝕜] E) := by
  constructor
  · rintro ⟨E, _, P, hP, e⟩
    exact ⟨E, ⟨P, hP⟩, e⟩
  · rintro ⟨E, hE, e⟩
    obtain ⟨P, hP⟩ := hE
    exact ⟨E, Submodule.ClosedComplemented.isClosed ⟨P, hP⟩, P, hP, e⟩

/-- X has a Cproj-complemented subspace Ciso-isomorphic to Y, using actual
bounded maps and an attained distortion bound. This does not use a
Banach–Mazur infimum or assert that such an infimum is attained. -/
def HasComplementedCopyWithBound (Cproj Ciso : ℝ) : Prop :=
  ∃ E : Submodule 𝕜 X, IsClosed (E : Set X) ∧
    ∃ P : X →L[𝕜] E, (∀ x : E, P (x : X) = x) ∧ ‖P‖ ≤ Cproj ∧
      IsomorphicWithBound 𝕜 Y E Ciso

theorem HasComplementedCopyWithBound.hasComplementedCopy {Cproj Ciso : ℝ}
    (h : HasComplementedCopyWithBound 𝕜 X Y Cproj Ciso) :
    HasComplementedCopy 𝕜 X Y := by
  obtain ⟨E, hE, P, hP, _, e, _⟩ := h
  exact ⟨E, hE, P, hP, ⟨e⟩⟩

/-- A retraction followed by the actual subspace inclusion is idempotent. -/
theorem complemented_retraction_projection (E : Submodule 𝕜 X)
    (P : X →L[𝕜] E) (hP : ∀ x : E, P (x : X) = x) :
    (E.subtypeL.comp P).comp (E.subtypeL.comp P) = E.subtypeL.comp P := by
  ext x
  exact congrArg Subtype.val (hP (P x))

/-- Passing from the subspace-valued retraction to the ambient projection
preserves its operator norm exactly, also when the subspace is zero. -/
theorem complemented_retraction_projection_norm (E : Submodule 𝕜 X)
    (P : X →L[𝕜] E) : ‖E.subtypeL.comp P‖ = ‖P‖ :=
  E.subtypeₗᵢ.norm_toContinuousLinearMap_comp

/-- The actual two-fold ℓp direct sum, including the maximum norm at infinity. -/
abbrev BanachDirectSum (p : BanachExponent) (X : Type u) (Y : Type v) :=
  WithLp p.val (X × Y)

theorem banachDirectSum_norm (p : BanachExponent) (hp : p.val ≠ ∞)
    (z : BanachDirectSum p X Y) :
    ‖z‖ = (‖z.fst‖ ^ p.val.toReal + ‖z.snd‖ ^ p.val.toReal) ^ (1 / p.val.toReal) := by
  exact WithLp.prod_norm_eq_add
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp) z

theorem banachDirectSum_norm_infty (z : BanachDirectSum ⟨∞, le_top⟩ X Y) :
    ‖z‖ = max ‖z.fst‖ ‖z.snd‖ := rfl

/-- The source Appendix A's auxiliary distortion bound a(Cproj,Ciso). -/
def decompositionAuxBound (Cproj Ciso : ℝ) : ℝ :=
  2 * (Real.sqrt Ciso + 1) * (Real.sqrt Ciso * Cproj + 1 + Cproj)

/-- The explicit admissible bound a² b² C5 C6 in Appendix A.1(a). -/
def decompositionSquareBound (C1 C2 C3 C4 C5 C6 : ℝ) : ℝ :=
  decompositionAuxBound C1 C2 ^ 2 * decompositionAuxBound C3 C4 ^ 2 * C5 * C6

/-- The explicit admissible bound a⁴ b⁴ C5⁴ in Appendix A.1(b). -/
def decompositionSequenceBound (C1 C2 C3 C4 C5 : ℝ) : ℝ :=
  decompositionAuxBound C1 C2 ^ 4 * decompositionAuxBound C3 C4 ^ 4 * C5 ^ 4

end ThesisCommon
