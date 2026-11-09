import BanachIsometric.CommutingStabilizerHomotopy

/-! Commutativity of the actual identity-component group forces its actual
infinitesimal kernel directions to commute: differentiate the two-parameter
exponential commutation identity twice. Thus the abelian-group case has
genuinely trivial higher homotopy, without a kernel-commutation premise. -/

namespace BanachIsometric

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem commute_of_commute_exp_smul (X Y : A)
    (h : ∀ s t : ℝ, Commute (NormedSpace.exp ℝ (s • X)) (NormedSpace.exp ℝ (t • Y))) :
    Commute X Y := by
  have hDX : HasDerivAt (fun s : ℝ => NormedSpace.exp ℝ (s • X)) X 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have hDY : HasDerivAt (fun t : ℝ => NormedSpace.exp ℝ (t • Y)) Y 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
  have he (t : ℝ) : X * NormedSpace.exp ℝ (t • Y) = NormedSpace.exp ℝ (t • Y) * X := by
    have hL := hDX.mul_const (NormedSpace.exp ℝ (t • Y))
    have hR := hDX.const_mul (NormedSpace.exp ℝ (t • Y))
    have hfun : (fun s : ℝ => NormedSpace.exp ℝ (s • X) * NormedSpace.exp ℝ (t • Y)) =
        (fun s : ℝ => NormedSpace.exp ℝ (t • Y) * NormedSpace.exp ℝ (s • X)) :=
      funext (fun s => (h s t).eq)
    rw [hfun] at hL
    exact hL.unique hR
  have hL := hDY.const_mul X
  have hR := hDY.mul_const X
  have hfun : (fun t : ℝ => X * NormedSpace.exp ℝ (t • Y)) =
      (fun t : ℝ => NormedSpace.exp ℝ (t • Y) * X) := funext he
  rw [hfun] at hL
  exact hL.unique hR

end Algebra

noncomputable section
namespace StabilizerLieCoordinates

open scoped Topology Topology.Homotopy

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ A] in
theorem commuting_kernel_of_abelian_identityComponent
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (hAbelian : ∀ R S : Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v),
      R * S = S * R)
    (X Y : kernel ρ v) :
    Commute (UnitaryOrbit.inclusion A (kernel ρ v) X) (UnitaryOrbit.inclusion A (kernel ρ v) Y) := by
  apply commute_of_commute_exp_smul
  intro s t
  have he := congrArg
    (fun R : Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v) =>
      (((R : unitaryRepresentationStabilizer ρ v) : unitary A) : A))
    (hAbelian (exponentialIdentityComponent ρ v horbit (s • X))
      (exponentialIdentityComponent ρ v horbit (t • Y)))
  change NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (kernel ρ v) (s • X)) *
      NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (kernel ρ v) (t • Y)) =
    NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (kernel ρ v) (t • Y)) *
      NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (kernel ρ v) (s • X)) at he
  simpa only [map_smul] using he

theorem subsingleton_higherHomotopy_of_abelian_identityComponent
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (hAbelian : ∀ R S : Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v),
      R * S = S * R)
    (n : ℕ) : Subsingleton (HomotopyGroup (Fin (n + 2))
      (Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) 1) :=
  subsingleton_higherHomotopy_identityComponent_of_commuting_kernel ρ v horbit
    (commuting_kernel_of_abelian_identityComponent ρ v horbit hAbelian) n

theorem isOfFinOrder_higherHomotopy_of_abelian_identityComponent
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (hAbelian : ∀ R S : Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v),
      R * S = S * R)
    (n : ℕ) (α : HomotopyGroup (Fin (n + 2))
      (Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) 1) : IsOfFinOrder α :=
  isOfFinOrder_higherHomotopy_identityComponent_of_commuting_kernel ρ v horbit
    (commuting_kernel_of_abelian_identityComponent ρ v horbit hAbelian) n α

end StabilizerLieCoordinates
end
end BanachIsometric
