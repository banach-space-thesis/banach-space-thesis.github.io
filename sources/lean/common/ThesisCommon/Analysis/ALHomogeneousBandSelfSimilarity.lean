import ThesisCommon.Analysis.ALPrincipalBandSelfCopies
import ThesisCommon.Analysis.ALFragmentDensityAtoms
import ThesisCommon.Analysis.ALHomogeneousPrincipalBands
import ThesisCommon.Analysis.ALFragmentNested

/-! Every atomless homogeneous principal AL band is genuinely isometric to
its countable ell-one sum. Geometric fragment division, actual homogeneous
matching, and norm-convergent band synthesis provide the isometry. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
  (e : E) [Fact (0 ≤ e)]
include hAL

theorem exists_ordered_principalBand_sequence_isometry_of_atomless_homogeneous
    (ha : NoPositiveAtomsBelow e)
    (hh : IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra e)) :
    ∃ d : principalBand e ≃ₗᵢ[ℝ] lp (fun _ : ℕ => principalBand e) 1,
      ∀ x, (∀ n, 0 ≤ d x n) ↔ 0 ≤ x := by
  obtain ⟨p, hp, hd, _, hsum, _⟩ :=
    exists_homogeneous_positiveFragment_geometric_partition hAL
      (⊤ : PositiveFragmentAlgebra e) ha hh
  let a : ℕ → E := fun n => positiveFragmentValue (p n)
  letI (n : ℕ) : Fact (0 ≤ a n) := ⟨positiveFragmentValue_nonneg (p n)⟩
  have hband (n : ℕ) : principalBand (a n) ≤ principalBand e := by
    apply principalBand_mono
    rw [abs_of_nonneg (positiveFragmentValue_nonneg (p n)), abs_of_nonneg (Fact.out : 0 ≤ e)]
    exact positiveFragmentValue_le (p n)
  have hdis : Pairwise (fun n m => |a n| ⊓ |a m| = 0) := by
    intro n m hnm
    rw [abs_of_nonneg (positiveFragmentValue_nonneg (p n)),
      abs_of_nonneg (positiveFragmentValue_nonneg (p m))]
    exact positiveFragmentValue_disjoint _ _ (hd hnm)
  have hinf : Cardinal.aleph0 ≤ topologicalDensity (PositiveFragmentAlgebra e) := by
    rw [← principalDensity_top]
    exact aleph0_le_principalDensity_of_atomless_positiveFragment hAL _ hh.1 ha
  have hmatching (n : ℕ) : ∃ d : principalBand (a n) ≃ₗᵢ[ℝ] principalBand e,
      ∀ x, 0 ≤ d x ↔ 0 ≤ x := by
    have hhpiece : IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra (a n)) :=
      (isDensityHomogeneous_top_positiveFragmentValue_iff e (p n)).mpr (hp n).2.2.1
    have hden : topologicalDensity (PositiveFragmentAlgebra (a n)) =
        topologicalDensity (PositiveFragmentAlgebra e) := by
      rw [topologicalDensity_positiveFragmentValue e (p n), (hp n).2.2.2, principalDensity_top]
    exact exists_ordered_principalBand_isometry_of_homogeneous hAL hAL (a n) e hhpiece hh
      hden (hden ▸ hinf)
  choose d hdpos using hmatching
  exact ⟨alPrincipalBandSequenceEquiv hAL e a hband hdis hsum d,
    alPrincipalBandSequenceEquiv_nonneg_iff hAL e a hband hdis hsum d hdpos⟩

theorem exists_orthogonal_selfCopies_atomless_homogeneous_principalBand
    (ha : NoPositiveAtomsBelow e)
    (hh : IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra e)) :
    ∃ J P : ℕ → principalBand e →L[ℝ] principalBand e,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id ℝ _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  obtain ⟨d, _⟩ := exists_ordered_principalBand_sequence_isometry_of_atomless_homogeneous hAL e ha hh
  exact exists_orthogonal_selfCopies_of_sequence_equiv d.toContinuousLinearEquiv

end ThesisCommon
