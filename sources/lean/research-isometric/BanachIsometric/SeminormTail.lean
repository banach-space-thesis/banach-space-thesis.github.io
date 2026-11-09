import BanachIsometric.SeminormInverseLimit

/-!
# Passing to a cofinal tail of an increasing defining seminorm sequence

Deleting finitely many seminorms preserves the original uniformity. Consequently
the canonical completed-quotient representation also applies to any tail, as
needed after the eventual dimension threshold in Theorem C.
-/

noncomputable section

namespace BanachIsometric

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- A larger seminorm induces a finer uniformity on the same algebraic module. -/
theorem seminormUniformSpace_antitone {p q : Seminorm ℂ X} (hpq : p ≤ q) :
    q.toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace ≤
      p.toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace := by
  let f : SeminormModel q →L[ℂ] SeminormModel p :=
    LinearMap.mkContinuous
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      1 (by intro x; simpa only [norm_seminormModel, one_mul] using hpq x)
  exact le_iff_uniformContinuous_id.mpr f.uniformContinuous

/-- Every cofinal tail of an increasing family generates the original topology
and uniformity, with the original scalar action unchanged. -/
theorem withSeminorms_tail [UniformSpace X] [IsUniformAddGroup X]
    (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) (hp : WithSeminorms p) (k₀ : ℕ) :
    WithSeminorms (fun k => p (k + k₀)) := by
  apply (SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf _).mpr
  rw [(SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf p).mp hp]
  apply le_antisymm
  · apply le_iInf
    intro k
    exact iInf_le _ (k + k₀)
  · apply le_iInf
    intro k
    exact (iInf_le _ k).trans
      (seminormUniformSpace_antitone (hmono (Nat.le_add_right k k₀)))

theorem seminormTail_monotone (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) (k₀ : ℕ) :
    Monotone (fun k => p (k + k₀)) := by
  intro i j hij
  exact hmono (Nat.add_le_add_right hij k₀)

/-- Canonical projective-limit representation after deleting any finite initial
segment. This uses the same original complete Hausdorff uniform space. -/
def seminormTailInverseLimitEquiv [UniformSpace X] [IsUniformAddGroup X]
    [CompleteSpace X] [T0Space X]
    (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) (hp : WithSeminorms p) (k₀ : ℕ) :
    X ≃L[ℂ] seminormLimitSubmodule (fun k => p (k + k₀))
      (seminormTail_monotone p hmono k₀) :=
  seminormInverseLimitEquiv (fun k => p (k + k₀))
    (seminormTail_monotone p hmono k₀) (withSeminorms_tail p hmono hp k₀)

@[simp] theorem seminormTailInverseLimitEquiv_apply
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]
    (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) (hp : WithSeminorms p)
    (k₀ : ℕ) (x : X) (i : ℕ) :
    (seminormTailInverseLimitEquiv p hmono hp k₀ x).val i =
      seminormCompletionMap (p (i + k₀)) x := rfl

end BanachIsometric
