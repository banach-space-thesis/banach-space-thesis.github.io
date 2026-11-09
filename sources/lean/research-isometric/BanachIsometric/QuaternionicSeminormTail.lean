import BanachIsometric.QuaternionicSeminormInverseLimit

/-! Deleting finitely many right-quaternionic seminorms preserves the actual
defining uniformity and canonical Hopp-linear inverse-limit representation. -/

namespace BanachIsometric.Quaternionic

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]

theorem seminormUniformSpace_antitone {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) :
    q.toRealSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace ≤
      p.toRealSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace := by
  let f : SeminormModel q →L[Hᵐᵒᵖ] SeminormModel p :=
    LinearMap.mkContinuous
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      1 (by intro x; simpa only [norm_seminormModel, one_mul] using hpq x)
  exact le_iff_uniformContinuous_id.mpr f.uniformContinuous

theorem withSeminorms_tail [UniformSpace X] [IsUniformAddGroup X]
    (p : ℕ → RightSeminorm X) (hmono : Monotone (fun i => (p i).toRealSeminorm))
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm)) (k₀ : ℕ) :
    WithSeminorms (fun k => (p (k + k₀)).toRealSeminorm) := by
  apply (SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf _).mpr
  rw [(SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf (fun i => (p i).toRealSeminorm)).mp hp]
  apply le_antisymm
  · apply le_iInf
    intro k
    exact iInf_le _ (k + k₀)
  · apply le_iInf
    intro k
    exact (iInf_le _ k).trans (seminormUniformSpace_antitone (hmono (Nat.le_add_right k k₀)))

theorem seminormTail_monotone (p : ℕ → RightSeminorm X)
    (hmono : Monotone (fun i => (p i).toRealSeminorm)) (k₀ : ℕ) :
    Monotone (fun k => (p (k + k₀)).toRealSeminorm) :=
  fun _ _ hij => hmono (Nat.add_le_add_right hij k₀)

def seminormTailInverseLimitEquiv [UniformSpace X] [IsUniformAddGroup X]
    [CompleteSpace X] [T0Space X] (p : ℕ → RightSeminorm X)
    (hmono : Monotone (fun i => (p i).toRealSeminorm))
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm)) (k₀ : ℕ) :
    X ≃L[Hᵐᵒᵖ] seminormLimitSubmodule (fun k => p (k + k₀)) (seminormTail_monotone p hmono k₀) :=
  seminormInverseLimitEquiv (fun k => p (k + k₀)) (seminormTail_monotone p hmono k₀)
    (withSeminorms_tail p hmono hp k₀)

@[simp] theorem seminormTailInverseLimitEquiv_apply
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]
    (p : ℕ → RightSeminorm X) (hmono : Monotone (fun i => (p i).toRealSeminorm))
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm)) (k₀ : ℕ) (x : X) (i : ℕ) :
    (seminormTailInverseLimitEquiv p hmono hp k₀ x).val i = seminormCompletionMap (p (i + k₀)) x := rfl

end
end BanachIsometric.Quaternionic
