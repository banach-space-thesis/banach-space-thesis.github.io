import ThesisCommon.Analysis.UncountableSchauderSumOperators

/-! Actual coordinate subspaces and projections for E(Γ,Y). The norm is
the norm-series norm already constructed, not a product topology norm. -/
noncomputable section
namespace ThesisCommon
namespace UncountableSchauderSum
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {b : NormalizedSchauderFamily 𝕜 Γ X} {hb : b.IsOneUnconditional}

/-- The source's E(A,Y), with the inherited norm. -/
def supportedSubmodule (A : Set Γ) : Submodule 𝕜 (UncountableSchauderSum b hb Y) where
  carrier := {x | ∀ γ, γ ∉ A → x γ = 0}
  zero_mem' := by simp
  add_mem' hx hy := by intro γ hγ; simp [hx γ hγ, hy γ hγ]
  smul_mem' c x hx := by intro γ hγ; simp [hx γ hγ]

abbrev SupportedSpace (A : Set Γ) := ↥(supportedSubmodule (b := b) (hb := hb) (Y := Y) A)

instance supportedSpace_normedAddCommGroup (A : Set Γ) :
    NormedAddCommGroup (SupportedSpace (b := b) (hb := hb) (Y := Y) A) :=
  inferInstanceAs (NormedAddCommGroup ↥(supportedSubmodule (b := b) (hb := hb) (Y := Y) A))

instance supportedSpace_normedSpace (A : Set Γ) :
    NormedSpace 𝕜 (SupportedSpace (b := b) (hb := hb) (Y := Y) A) :=
  inferInstanceAs (NormedSpace 𝕜 ↥(supportedSubmodule (b := b) (hb := hb) (Y := Y) A))

theorem supportedSubmodule_isClosed (A : Set Γ) :
    IsClosed (supportedSubmodule (b := b) (hb := hb) (Y := Y) A :
      Set (UncountableSchauderSum b hb Y)) := by
  change IsClosed {x : UncountableSchauderSum b hb Y |
    ∀ γ, γ ∉ A → coordinate (b := b) (hb := hb) (Y := Y) γ x = 0}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun γ => isClosed_iInter fun _ =>
    isClosed_eq (coordinate (b := b) (hb := hb) (Y := Y) γ).continuous continuous_const

instance supportedSpace_completeSpace [CompleteSpace Y] (A : Set Γ) :
    CompleteSpace (SupportedSpace (b := b) (hb := hb) (Y := Y) A) :=
  (supportedSubmodule_isClosed (b := b) (hb := hb) (Y := Y) A).completeSpace_coe

/-- The actual coordinate suppression R_A. -/
def coordinateProjection (A : Set Γ) :
    UncountableSchauderSum b hb Y →L[𝕜] UncountableSchauderSum b hb Y :=
  LinearMap.mkContinuous
    { toFun := fun x => ofDominated x (fun γ => if γ ∈ A then x γ else 0)
        zero_le_one (fun γ => by by_cases h : γ ∈ A <;> simp [h])
      map_add' := by intro x y; ext γ; by_cases h : γ ∈ A <;> simp [h]
      map_smul' := by intro c x; ext γ; by_cases h : γ ∈ A <;> simp [h] }
    1 (fun x => norm_ofDominated_le x
      (fun γ => if γ ∈ A then x γ else 0) zero_le_one
        (fun γ => by by_cases h : γ ∈ A <;> simp [h]))

@[simp] theorem coordinateProjection_apply (A : Set Γ)
    (x : UncountableSchauderSum b hb Y) (γ : Γ) :
    coordinateProjection (b := b) (hb := hb) (Y := Y) A x γ =
      if γ ∈ A then x γ else 0 := rfl

theorem norm_coordinateProjection_le (A : Set Γ) :
    ‖coordinateProjection (b := b) (hb := hb) (Y := Y) A‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem coordinateProjection_idempotent (A : Set Γ) :
    (coordinateProjection (b := b) (hb := hb) (Y := Y) A).comp
      (coordinateProjection A) = coordinateProjection A := by
  ext x γ
  by_cases h : γ ∈ A <;> simp [h]

def projectionTo (A : Set Γ) :
    UncountableSchauderSum b hb Y →L[𝕜] SupportedSpace (b := b) (hb := hb) (Y := Y) A :=
  (coordinateProjection (b := b) (hb := hb) (Y := Y) A).codRestrict
    (supportedSubmodule (b := b) (hb := hb) (Y := Y) A)
    (fun x γ hγ => by simp [hγ])

theorem projectionTo_subtype (A : Set Γ) :
    (projectionTo (b := b) (hb := hb) (Y := Y) A).comp
      (supportedSubmodule A).subtypeL = ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  apply UncountableSchauderSum.ext
  intro γ
  change (if γ ∈ A then x.val γ else 0) = x.val γ
  by_cases h : γ ∈ A
  · simp [h]
  · simp [h, x.property γ h]

end UncountableSchauderSum
end ThesisCommon
