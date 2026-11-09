import SurveyStatements.P4DFJPApproximation
import SurveyStatements.P4FiniteDecomposition

/-! Compatible ambient projections induce a genuine finite decomposition
of the actual gauge space, with no assumed interpolation conclusions. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Set Filter Topology

namespace SurveyStatements.P4.DFJPSpace

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

theorem finiteDecomposition_of_contractions
    (D : DFJPGaugeData 𝕜 E) (T : ℕ → E →L[𝕜] E)
    (hK : ∀ n, ∀ x ∈ D.carrier, T n x ∈ D.carrier) (hT : ∀ n, ‖T n‖ ≤ 1)
    (hpoint : ∀ x : E, Tendsto (fun n => T n x) atTop (𝓝 x))
    (hcomp : ∀ n m, (T n).comp (T m) = T (min n m))
    (F : ℕ → Submodule 𝕜 E) [∀ n, FiniteDimensional 𝕜 (F n)]
    (hF : ∀ n, ∀ x ∈ closure (Submodule.span 𝕜 D.carrier : Set E), T n x ∈ F n) :
    Nonempty (ContractiveFiniteDecomposition 𝕜 (DFJPSpace D)) := by
  let C := fun n => contraction D (T n) (hK n) (hT n)
  let P : ℕ → DFJPSpace D →L[𝕜] DFJPSpace D :=
    fun n => Nat.casesOn n 0 C
  have hPzero : P 0 = 0 := rfl
  have hPsucc (n : ℕ) : P (n + 1) = C n := rfl
  refine ⟨{ projection := P
            zero := hPzero
            finiteRank := ?_
            norm_le := ?_
            comp := ?_
            tendsto := ?_ }⟩
  · intro n
    cases n with
    | zero => rw [hPzero]; exact finiteRank_zero
    | succ n =>
        rw [hPsucc]
        exact contraction_hasFiniteRank D (T n) (hK n) (hT n) (F n) (hF n)
  · intro n
    cases n with
    | zero => rw [hPzero, norm_zero]; norm_num
    | succ n => rw [hPsucc]; exact norm_contraction_le_one D (T n) (hK n) (hT n)
  · intro n m
    cases n with
    | zero => simp [hPzero]
    | succ n =>
        cases m with
        | zero => simp [hPzero]
        | succ m =>
            have hmin : min (n + 1) (m + 1) = min n m + 1 := by omega
            rw [hmin, hPsucc, hPsucc, hPsucc]
            exact contraction_comp_of_eq D (T n) (T m) (T (min n m))
              (hK n) (hT n) (hK m) (hT m) (hK _) (hT _) (hcomp n m)
  · intro f
    apply (tendsto_add_atTop_iff_nat 1).mp
    simp only [hPsucc]
    exact tendsto_contractions D T hK hT hpoint f

end SurveyStatements.P4.DFJPSpace
