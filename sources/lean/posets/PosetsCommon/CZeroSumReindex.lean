import PosetsCommon.CZeroSum

/-! Isometric reindexing of dependent c₀ sums along an arbitrary equivalence. -/

noncomputable section
namespace ThesisCommon
open Filter Topology
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {P Q : Type*} (e : P ≃ Q)
variable (X : Q → Type*) [∀ q, NormedAddCommGroup (X q)] [∀ q, NormedSpace 𝕜 (X q)]

def cZeroSumReindexValue (f : DependentCZeroSum 𝕜 (fun p => X (e p))) :
    DependentCZeroSum 𝕜 X :=
  ⟨⟨Equiv.piCongrLeft X e f.val, memℓp_infty ⟨‖f‖, by
    rintro _ ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ := e.surjective q
    simpa only [Equiv.piCongrLeft_apply_apply] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero f.val p⟩⟩, by
    change Tendsto (fun q => ‖Equiv.piCongrLeft X e f.val q‖) cofinite (𝓝 0)
    have h : Tendsto ((fun q => ‖Equiv.piCongrLeft X e f.val q‖) ∘ e) cofinite (𝓝 0) := by
      simpa only [Function.comp_def, Equiv.piCongrLeft_apply_apply] using f.property
    exact (tendsto_map'_iff.mpr h).mono_left e.surjective.le_map_cofinite⟩

@[simp] theorem cZeroSumReindexValue_apply (f : DependentCZeroSum 𝕜 (fun p => X (e p))) (p : P) :
    (cZeroSumReindexValue e X f).val (e p) = f.val p := Equiv.piCongrLeft_apply_apply _ _ _ _

def cZeroSumReindexPull (f : DependentCZeroSum 𝕜 X) :
    DependentCZeroSum 𝕜 (fun p => X (e p)) :=
  ⟨⟨fun p => f.val (e p), memℓp_infty ⟨‖f‖, by
    rintro _ ⟨p, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f.val (e p)⟩⟩,
    f.property.comp e.injective.tendsto_cofinite⟩

theorem cZeroSumReindexValue_norm (f : DependentCZeroSum 𝕜 (fun p => X (e p))) :
    ‖cZeroSumReindexValue e X f‖ = ‖f‖ := by
  apply le_antisymm
  · apply lp.norm_le_of_forall_le (norm_nonneg f)
    intro q
    obtain ⟨p, rfl⟩ := e.surjective q
    change ‖(cZeroSumReindexValue e X f).val (e p)‖ ≤ ‖f‖
    rw [cZeroSumReindexValue_apply]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f.val p
  · apply lp.norm_le_of_forall_le (norm_nonneg (cZeroSumReindexValue e X f))
    intro p
    change ‖f.val p‖ ≤ ‖cZeroSumReindexValue e X f‖
    rw [← cZeroSumReindexValue_apply e X f p]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (cZeroSumReindexValue e X f).val (e p)

def cZeroSumReindexEquiv : DependentCZeroSum 𝕜 (fun p => X (e p)) ≃ₗᵢ[𝕜]
    DependentCZeroSum 𝕜 X where
  toFun := cZeroSumReindexValue e X
  invFun := cZeroSumReindexPull e X
  left_inv f := by
    apply Subtype.ext
    apply lp.ext
    funext p
    exact cZeroSumReindexValue_apply e X f p
  right_inv f := by
    apply Subtype.ext
    apply lp.ext
    funext q
    obtain ⟨p, rfl⟩ := e.surjective q
    exact cZeroSumReindexValue_apply e X _ p
  map_add' f g := by
    apply Subtype.ext
    apply lp.ext
    funext q
    obtain ⟨p, rfl⟩ := e.surjective q
    change (cZeroSumReindexValue e X (f + g)).val (e p) =
      (cZeroSumReindexValue e X f).val (e p) + (cZeroSumReindexValue e X g).val (e p)
    simp only [cZeroSumReindexValue_apply]
    rfl
  map_smul' a f := by
    apply Subtype.ext
    apply lp.ext
    funext q
    obtain ⟨p, rfl⟩ := e.surjective q
    change (cZeroSumReindexValue e X (a • f)).val (e p) =
      a • (cZeroSumReindexValue e X f).val (e p)
    simp only [cZeroSumReindexValue_apply]
    rfl
  norm_map' := cZeroSumReindexValue_norm e X

@[simp] theorem cZeroSumReindexEquiv_apply (f : DependentCZeroSum 𝕜 (fun p => X (e p))) (p : P) :
    ((cZeroSumReindexEquiv e X) f).val (e p) = f.val p := cZeroSumReindexValue_apply e X f p

@[simp] theorem cZeroSumReindexEquiv_symm_apply (f : DependentCZeroSum 𝕜 X) (p : P) :
    (((cZeroSumReindexEquiv e X).symm) f).val p = f.val (e p) := rfl

end ThesisCommon
