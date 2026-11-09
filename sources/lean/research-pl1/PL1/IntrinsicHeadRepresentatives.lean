import PL1.IntrinsicWalsh
import PL1.HeadTail

/-!
# Continuous head representatives of intrinsic finite-coordinate vectors

Every coordinate of a vector in the actual intrinsic expectation range has a
continuous representative depending only on the prescribed initial segment.
The equalities below are identities in the original Haar L¹ quotient.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.IntrinsicHeadRepresentatives
open Walsh WalshExpectations IntrinsicGraph Noise

variable {K : Type*} [RCLike K]

theorem scalarCharacter_dependsOn (m : ℕ) (F : Finset ℕ) (hF : F ⊆ Finset.range m) :
    HeadTail.DependsOn (Finset.range m) (scalarCharacterContinuous K F) := by
  intro x y hxy
  change (character F x : K) = (character F y : K)
  congr 1
  unfold character
  apply Finset.prod_congr rfl
  intro j hj
  exact congrArg signValue (hxy j (hF hj))

theorem continuousRepresentative_of_mem_finiteSpan (m : ℕ) {f : Lp K 1 haar}
    (hf : f ∈ finiteSpan K m) :
    ∃ g : C(Walsh.Group, K), HeadTail.DependsOn (Finset.range m) g ∧
      ContinuousMap.toLp 1 haar K g = f := by
  let H : Submodule K (Lp K 1 haar) := {
    carrier := {f | ∃ g : C(Walsh.Group, K), HeadTail.DependsOn (Finset.range m) g ∧
      ContinuousMap.toLp 1 haar K g = f}
    zero_mem' := ⟨0, (fun _ _ _ => rfl), map_zero _⟩
    add_mem' := by
      rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
      refine ⟨g + h, ?_, map_add _ _ _⟩
      intro x y hxy
      simp only [ContinuousMap.add_apply, hg x y hxy, hh x y hxy]
    smul_mem' := by
      rintro c _ ⟨g, hg, rfl⟩
      refine ⟨c • g, ?_, map_smul _ _ _⟩
      intro x y hxy
      simp only [ContinuousMap.smul_apply, hg x y hxy]
  }
  have hle : finiteSpan K m ≤ H := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨scalarCharacterContinuous K F,
      scalarCharacter_dependsOn m F (Finset.mem_powerset.mp hF),
      toLp_scalarCharacterContinuous K 1 F⟩
  exact hle hf

theorem analysis_mem_finiteSpan (rates : ℕ → ℝ≥0) (m n : ℕ)
    {f : Lp K 1 haar} (hf : f ∈ finiteSpan K m) :
    (dyadicSystem K rates).analysis n f ∈ finiteSpan K m := by
  have hle : finiteSpan K m ≤ (finiteSpan K m).comap
      ((dyadicSystem K rates).analysis n).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F, hF, rfl⟩
    have hmem := character_mem_finiteSpan K m F (Finset.mem_powerset.mp hF)
    change (dyadicSystem K rates).analysis n (scalarCharacterLp K 1 F) ∈ finiteSpan K m
    cases n with
    | zero => exact hmem
    | succ n =>
      change (((ResolventEstimates.dyadicRatio ^ (n + 1))⁻¹ : ℝ) : K) •
          (scalarCharacterLp K 1 F - resolventL1 K rates (dyadicTime (n + 1))
            (scalarCharacterLp K 1 F)) ∈ finiteSpan K m
      rw [resolventL1_scalarCharacter]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hmem (Submodule.smul_mem _ _ hmem))
  exact hle hf

theorem coord_mem_finiteSpan_of_range (rates : ℕ → ℝ≥0) (m n : ℕ)
    {f : (dyadicSystem K rates).IntrinsicSpace}
    (hf : f ∈ (intrinsicExpectation K rates m).range) :
    coord (dyadicSystem K rates).analysis n f ∈ finiteSpan K m := by
  obtain ⟨g, rfl⟩ := hf
  change coord (dyadicSystem K rates).analysis n (intrinsicExpectation K rates m g) ∈
    finiteSpan K m
  rw [coord_intrinsicExpectation]
  exact expectationL1_mem_finiteSpan K m _

theorem continuousRepresentative_coord_of_range (rates : ℕ → ℝ≥0) (m n : ℕ)
    {f : (dyadicSystem K rates).IntrinsicSpace}
    (hf : f ∈ (intrinsicExpectation K rates m).range) :
    ∃ g : C(Walsh.Group, K), HeadTail.DependsOn (Finset.range m) g ∧
      ContinuousMap.toLp 1 haar K g = coord (dyadicSystem K rates).analysis n f :=
  continuousRepresentative_of_mem_finiteSpan m (coord_mem_finiteSpan_of_range rates m n hf)

theorem continuousRepresentative_evalZero_of_range (rates : ℕ → ℝ≥0) (m : ℕ)
    {f : (dyadicSystem K rates).IntrinsicSpace}
    (hf : f ∈ (intrinsicExpectation K rates m).range) :
    ∃ g : C(Walsh.Group, K), HeadTail.DependsOn (Finset.range m) g ∧
      ContinuousMap.toLp 1 haar K g = evalZero (dyadicSystem K rates).analysis f :=
  continuousRepresentative_coord_of_range rates m 0 hf

end PL1.IntrinsicHeadRepresentatives
