import Posets.SzlenkIdealRank
import Posets.SzlenkIdealComposition
import Mathlib.Analysis.Normed.Operator.Prod

/-! Addition stability from two-coordinate derivative ranks. The analytic
argument applies at every ordinal closed under finite natural sums. -/

noncomputable section
open Set Topology
open scoped NaturalOps
namespace Posets
variable {𝕜 E F G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem strongDual_prod_norm_le (φ : StrongDual 𝕜 (E × F)) :
    ‖φ‖ ≤ ‖φ.comp (ContinuousLinearMap.inl 𝕜 E F)‖ +
      ‖φ.comp (ContinuousLinearMap.inr 𝕜 E F)‖ := by
  let a := φ.comp (ContinuousLinearMap.inl 𝕜 E F)
  let b := φ.comp (ContinuousLinearMap.inr 𝕜 E F)
  have he : φ = a.comp (ContinuousLinearMap.fst 𝕜 E F) +
      b.comp (ContinuousLinearMap.snd 𝕜 E F) := by
    dsimp [a, b]
    rw [ContinuousLinearMap.comp_fst_add_comp_snd, ← ContinuousLinearMap.comp_coprod,
      ContinuousLinearMap.coprod_inl_inr, ContinuousLinearMap.comp_id]
  calc
    ‖φ‖ = ‖a.comp (ContinuousLinearMap.fst 𝕜 E F) +
        b.comp (ContinuousLinearMap.snd 𝕜 E F)‖ := congrArg norm he
    _ ≤ ‖a.comp (ContinuousLinearMap.fst 𝕜 E F)‖ +
        ‖b.comp (ContinuousLinearMap.snd 𝕜 E F)‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖ContinuousLinearMap.fst 𝕜 E F‖ +
        ‖b‖ * ‖ContinuousLinearMap.snd 𝕜 E F‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖a‖ + ‖b‖ := by
      simpa only [mul_one] using add_le_add
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_fst_le 𝕜 E F) (norm_nonneg a))
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le 𝕜 E F) (norm_nonneg b))

theorem OperatorSzlenkBound.coprod {κ : Ordinal}
    (hκ : ∀ a < κ, ∀ b < κ, a ♯ b < κ)
    {S : E →L[𝕜] G} {T : F →L[𝕜] G}
    (hS : OperatorSzlenkBound S κ) (hT : OperatorSzlenkBound T κ) :
    OperatorSzlenkBound (S.coprod T) κ := by
  intro ε hε
  let p := weakStarAdjoint (ContinuousLinearMap.inl 𝕜 E F)
  let q := weakStarAdjoint (ContinuousLinearMap.inr 𝕜 E F)
  have hpH : ∀ x ∈ adjointUnitBall (S.coprod T), p x ∈ adjointUnitBall S := by
    intro x hx
    have hh : p x ∈ weakStarAdjoint (ContinuousLinearMap.inl 𝕜 E F) ''
        adjointUnitBall (S.coprod T) := ⟨x, hx, rfl⟩
    rwa [← adjointUnitBall_comp, ContinuousLinearMap.coprod_comp_inl] at hh
  have hqH : ∀ x ∈ adjointUnitBall (S.coprod T), q x ∈ adjointUnitBall T := by
    intro x hx
    have hh : q x ∈ weakStarAdjoint (ContinuousLinearMap.inr 𝕜 E F) ''
        adjointUnitBall (S.coprod T) := ⟨x, hx, rfl⟩
    rwa [← adjointUnitBall_comp, ContinuousLinearMap.coprod_comp_inr] at hh
  have hd : ∀ x ∈ adjointUnitBall (S.coprod T),
      ∀ y ∈ adjointUnitBall (S.coprod T),
      ‖WeakDual.toStrongDual x - WeakDual.toStrongDual y‖ ≤
        ‖WeakDual.toStrongDual (p x) - WeakDual.toStrongDual (p y)‖ +
        ‖WeakDual.toStrongDual (q x) - WeakDual.toStrongDual (q y)‖ := by
    intro x _ y _
    change ‖WeakDual.toStrongDual x - WeakDual.toStrongDual y‖ ≤
      ‖(WeakDual.toStrongDual x).comp (ContinuousLinearMap.inl 𝕜 E F) -
        (WeakDual.toStrongDual y).comp (ContinuousLinearMap.inl 𝕜 E F)‖ +
      ‖(WeakDual.toStrongDual x).comp (ContinuousLinearMap.inr 𝕜 E F) -
        (WeakDual.toStrongDual y).comp (ContinuousLinearMap.inr 𝕜 E F)‖
    simpa only [ContinuousLinearMap.sub_comp] using
      strongDual_prod_norm_le (WeakDual.toStrongDual x - WeakDual.toStrongDual y)
  have hi := szlenkIterate_pair_empty p q (weakStarAdjoint_continuous _)
    (weakStarAdjoint_continuous _) (adjointUnitBall_isCompact S).isClosed
    (adjointUnitBall_isCompact T).isClosed hpH hqH hd hκ
    (hS (ε / 2) (by positivity)) (hT (ε / 2) (by positivity))
  have hεeq : 2 * (ε / 2) = ε := by ring
  rwa [hεeq] at hi

theorem OperatorSzlenkBound.add {κ : Ordinal}
    (hκ : ∀ a < κ, ∀ b < κ, a ♯ b < κ)
    {S T : E →L[𝕜] F} (hS : OperatorSzlenkBound S κ) (hT : OperatorSzlenkBound T κ) :
    OperatorSzlenkBound (S + T) κ := by
  have hh := (hS.coprod hκ hT).precomp
    ((ContinuousLinearMap.id 𝕜 E).prod (ContinuousLinearMap.id 𝕜 E))
  have he : (S.coprod T).comp
      ((ContinuousLinearMap.id 𝕜 E).prod (ContinuousLinearMap.id 𝕜 E)) = S + T := by
    ext x
    rfl
  rwa [he] at hh

end Posets
