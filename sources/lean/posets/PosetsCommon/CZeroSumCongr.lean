import PosetsCommon.CZeroSum

/-! Coordinatewise linear isometries induce a linear isometry of genuine
dependent c₀ sums, including empty index and zero coordinate spaces. -/

noncomputable section
namespace ThesisCommon
open Filter Topology
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {P : Type*}
variable {X Y : P → Type*} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace 𝕜 (Y p)]

def cZeroSumCongrValue (e : ∀ p, X p ≃ₗᵢ[𝕜] Y p) (f : DependentCZeroSum 𝕜 X) :
    DependentCZeroSum 𝕜 Y :=
  ⟨⟨fun p => e p (f.val p), memℓp_infty ⟨‖f‖, by
    rintro _ ⟨p, rfl⟩
    simpa only [LinearIsometryEquiv.norm_map] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero f.val p⟩⟩, by
    change Tendsto (fun p => ‖e p (f.val p)‖) cofinite (𝓝 0)
    simpa only [LinearIsometryEquiv.norm_map] using f.property⟩

def cZeroSumCongrEquiv (e : ∀ p, X p ≃ₗᵢ[𝕜] Y p) :
    DependentCZeroSum 𝕜 X ≃ₗᵢ[𝕜] DependentCZeroSum 𝕜 Y where
  toFun := cZeroSumCongrValue e
  invFun := cZeroSumCongrValue (fun p => (e p).symm)
  left_inv f := by
    apply Subtype.ext
    apply lp.ext
    funext p
    exact (e p).symm_apply_apply (f.val p)
  right_inv f := by
    apply Subtype.ext
    apply lp.ext
    funext p
    exact (e p).apply_symm_apply (f.val p)
  map_add' f g := by
    apply Subtype.ext
    apply lp.ext
    funext p
    exact map_add (e p) (f.val p) (g.val p)
  map_smul' a f := by
    apply Subtype.ext
    apply lp.ext
    funext p
    exact map_smul (e p) a (f.val p)
  norm_map' f := by
    change (⨆ p, ‖e p (f.val p)‖) = ⨆ p, ‖f.val p‖
    simp only [LinearIsometryEquiv.norm_map]

@[simp] theorem cZeroSumCongrEquiv_apply (e : ∀ p, X p ≃ₗᵢ[𝕜] Y p)
    (f : DependentCZeroSum 𝕜 X) (p : P) :
    ((cZeroSumCongrEquiv e) f).val p = e p (f.val p) := rfl

end ThesisCommon
