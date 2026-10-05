import ThesisCommon.Analysis.ALTotalHomogeneousBands
import ThesisCommon.Analysis.ALBandDecomposition
import ThesisCommon.Analysis.ALHomogeneousBandSelfSimilarity
import ThesisCommon.Analysis.ALFragmentAtomDichotomy
import ThesisCommon.Analysis.ALAtomicFamilyCornerCopies
import ThesisCommon.Analysis.ALDedekindComplete
import ThesisCommon.Analysis.EllOneFamilyTranspose
import ThesisCommon.Analysis.EllOneFamilySplit
import ThesisCommon.Analysis.OperatorAlgebraCornerTransport

/-! Every complete real AL-lattice has countably many orthogonal copies
of one common corner, with weakly compact complementary identity. The
corner is assembled from actual homogeneous principal bands. Atomic
families are treated separately, so a finite atomic remainder is allowed.
All arbitrary-family assembly uses onto linear isometries, hence uniform
coordinate bounds; neither separability nor a classification premise is
assumed. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]

theorem exists_real_AL_orthogonal_cornerCopies
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖) :
    ∃ Q : E →L[ℝ] E, ∃ J P : ℕ → E →L[ℝ] E,
      (∀ n, (P n).comp (J n) = Q) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) ∧
      IsWeaklyCompactOperator (ContinuousLinearMap.id ℝ E - Q) := by
  letI : ConditionallyCompleteLattice E := alConditionallyCompleteLattice hAL
  obtain ⟨S, hpos, hdis, htotal⟩ := exists_total_homogeneous_positive_family (E := E)
  let a : S → E := Subtype.val
  have ha : ∀ i, 0 ≤ a i := fun i => (hpos i i.property).1
  have hd : Pairwise (fun i j : S => |a i| ⊓ |a j| = 0) := by
    intro i j hij
    rw [abs_of_nonneg (ha i), abs_of_nonneg (ha j)]
    exact hdis i.property j.property (fun h => hij (Subtype.ext h))
  have ht : ∀ x : E, 0 ≤ x → (∀ i, x ⊓ a i = 0) → x = 0 := by
    intro x hx hh
    exact htotal x hx (fun e he => hh ⟨e, he⟩)
  let A : Set S := {i | IsPositiveLatticeAtom (a i)}
  let F : S → Type _ := fun i => principalBand (a i)
  let X := lp (fun i : A => F i.val) 1
  let Y := lp (fun i : (Aᶜ : Set S) => F i.val) 1
  obtain ⟨QX, JX, PX, hdX, hoX, hrX⟩ :=
    exists_orthogonal_cornerCopies_atomic_principalBand_family hAL
      (fun i : A => a i.val) (fun i => i.property)
  have hseq (i : (Aᶜ : Set S)) :
      Nonempty (F i.val ≃ₗᵢ[ℝ] lp (fun _ : ℕ => F i.val) 1) := by
    obtain ⟨hx, hh⟩ := (hpos i.val i.val.property).2.2
    letI : Fact (0 ≤ a i.val) := ⟨hx⟩
    have hno : NoPositiveAtomsBelow (a i.val) := by
      have h := isPositiveLatticeAtom_or_noPositiveAtomsBelow_of_densityHomogeneous hAL
        (⊤ : PositiveFragmentAlgebra (a i.val)) hh
      simp only [positiveFragmentValue_top] at h
      exact h.resolve_left i.property
    obtain ⟨d, _⟩ := exists_ordered_principalBand_sequence_isometry_of_atomless_homogeneous
      hAL (a i.val) hno hh
    exact ⟨d⟩
  let d (i : (Aᶜ : Set S)) := (hseq i).some
  obtain ⟨JY, PY, hdY, hoY⟩ := exists_orthogonal_selfCopies_ellOne_family d
  have hrY : IsWeaklyCompactOperator
      (ContinuousLinearMap.id ℝ Y - ContinuousLinearMap.id ℝ Y) := by
    simpa only [sub_self] using (weaklyCompact_zero (𝕜 := ℝ) (E := Y) (F := Y))
  obtain ⟨Q, J, P, hdiag, hoff, hrem⟩ := exists_orthogonal_cornerCopies_prod
    QX JX PX hdX hoX hrX (ContinuousLinearMap.id ℝ Y) JY PY hdY hoY hrY
  let b := (alBandIsometryEquiv hAL a ha hd ht).toContinuousLinearEquiv
  let c := ellOneFamilySplit (𝕜 := ℝ) (E := F) A
  exact exists_orthogonal_cornerCopies_of_equiv (b.trans c) Q J P hdiag hoff hrem

end ThesisCommon
