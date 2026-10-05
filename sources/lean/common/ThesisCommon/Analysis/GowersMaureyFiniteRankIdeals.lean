import ThesisCommon.Analysis.NonzeroOperatorIdeals
import ThesisCommon.Analysis.GowersMaureyStrictlySingularIdeal
import ThesisCommon.Analysis.GowersMaureyShiftDefects
import ThesisCommon.Analysis.GowersMaureyInfiniteDimensional

/-! Every maximal two-sided operator ideal on the actual shift space contains
all finite-rank maps. The genuinely strictly singular ideal supplies a
nonzero proper intermediate ideal, so a maximal ideal cannot be zero.
Containment of every strictly singular operator is a separate obligation. -/
noncomputable section
namespace ThesisCommon

theorem isCoatom_ne_bot_of_nonzero_proper_twoSidedIdeal
    {R : Type*} [Ring R] (J I : TwoSidedIdeal R) (hJ : IsCoatom J)
    (hI : I ≠ ⊥) (hI' : I ≠ ⊤) : J ≠ ⊥ := by
  intro hzero
  have hle : J ≤ I := by rw [hzero]; exact bot_le
  have hi : I ≤ J := (isCoatom_iff_ge_of_le.mp hJ).2 I hI' hle
  rw [hzero] at hi
  exact hI (le_antisymm hi bot_le)

namespace GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem strictlySingularIdeal_ne_bot (D : ConstructionData 𝕜) :
    strictlySingularIdeal D ≠ ⊥ := by
  let P := (completedCoordinate D 0).smulRight (basisVector D 0)
  have hp : P ∈ strictlySingularIdeal D := by
    apply (mem_strictlySingularIdeal D P).mpr
    change IsStrictlySingularOperator ((completedCoordinate D 0).smulRight (basisVector D 0))
    rw [← completedSpread_right_left_defect]
    exact completedSpread_defect_strictlySingular D
  have hp0 : P ≠ 0 := by
    intro h
    have hh := congrArg (fun A : ShiftSpace D →L[𝕜] ShiftSpace D =>
      completedCoordinate D 0 (A (basisVector D 0))) h
    simp [P] at hh
  intro hbot
  rw [hbot, TwoSidedIdeal.mem_bot] at hp
  exact hp0 hp

theorem strictlySingularIdeal_ne_top (D : ConstructionData 𝕜) :
    strictlySingularIdeal D ≠ ⊤ := by
  intro htop
  have hi : ContinuousLinearMap.id 𝕜 (ShiftSpace D) ∈ strictlySingularIdeal D := by
    rw [htop]
    trivial
  have hss := (mem_strictlySingularIdeal D _).mp hi
  have hfd := hss (⊤ : Submodule 𝕜 (ShiftSpace D))
    ⟨1, zero_lt_one, fun x => by simp⟩
  letI := hfd
  apply shiftSpace_infiniteDimensional D
  exact FiniteDimensional.of_surjective (⊤ : Submodule 𝕜 (ShiftSpace D)).subtype
    (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩)

theorem maximalOperatorIdeal_ne_bot (D : ConstructionData 𝕜)
    (J : TwoSidedIdeal (ShiftSpace D →L[𝕜] ShiftSpace D)) (hJ : IsCoatom J) : J ≠ ⊥ :=
  isCoatom_ne_bot_of_nonzero_proper_twoSidedIdeal J (strictlySingularIdeal D) hJ
    (strictlySingularIdeal_ne_bot D) (strictlySingularIdeal_ne_top D)

theorem finiteRank_mem_maximalOperatorIdeal (D : ConstructionData 𝕜)
    (J : TwoSidedIdeal (ShiftSpace D →L[𝕜] ShiftSpace D)) (hJ : IsCoatom J)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D)
    [FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)] : T ∈ J :=
  finiteRank_mem_twoSidedIdeal_of_ne_bot J (maximalOperatorIdeal_ne_bot D J hJ) T

end GowersMaurey
end ThesisCommon
