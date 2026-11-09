import BanachIsometric.HermitianGlobalProportionality
import BanachIsometric.ComplexPolarization

/-!
# Proportionality for the original complex Hermitian norms

The first norm and original complex action are preserved. Its explicit
Hermitian-square witness supplies a compatible inner product. The second
given form is bundled algebraically and fed to the proved Riesz/spectral/global
argument. No representing operator or spectral conclusion is an assumption.
-/

namespace BanachIsometric

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

def PositiveHermitianForm.toSesqLinear (h : PositiveHermitianForm X) :
    X →ₗ⋆[ℂ] X →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := h.form x
      map_add' := h.add_right x
      map_smul' := fun a y => h.smul_right x y a }
  map_add' x y := by
    ext z
    exact h.map_add_left x y z
  map_smul' a x := by
    ext y
    exact h.map_smul_left a x y

@[simp]
theorem PositiveHermitianForm.toSesqLinear_apply (h : PositiveHermitianForm X) (x y : X) :
    h.toSesqLinear x y = h.form x y := rfl

section Norm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The spectral/global step for two actual Hermitian norms, expressed using
the original paper's explicit form witnesses and shared complex-linear section
similarities. The first existing norm and its complex action are unchanged. -/
theorem complex_norm_proportional_of_hermitian_similarities
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ E)
    (hp : HasHermitianSquare (norm : E → ℝ)) {q : E → ℝ}
    (hq : HasHermitianSquare q) (hqnonneg : ∀ x, 0 ≤ q x)
    (hsim : SimultaneousPairSimilarities (𝕜 := ℂ) n norm q) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * ‖x‖ := by
  obtain ⟨pForm, hpForm⟩ := hp
  letI : InnerProductSpace ℂ E := pForm.toInnerProductSpace hpForm
  obtain ⟨qForm, hqForm⟩ := hq
  apply hermitianNorm_global_proportional_of_simultaneous_similarities hn hdim
    qForm.toSesqLinear qForm.conj_symm qForm.self_pos q hqnonneg _ hsim
  intro x
  exact congrArg Complex.re (hqForm x)

end Norm

end

end BanachIsometric
