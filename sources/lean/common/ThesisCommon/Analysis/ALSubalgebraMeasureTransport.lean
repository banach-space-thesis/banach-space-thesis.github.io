import ThesisCommon.Analysis.ALSubalgebraMeasureAlgebra
import ThesisCommon.Analysis.MeasureAlgebraL1

/-! A content-preserving isomorphism of closed fragment subalgebras induces
an actual isomorphism of their generated, trimmed measure algebras. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
  [HasSolidNorm F] [CompleteSpace F]
variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]
variable (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (f : F) [Fact (0 ≤ f)]

def alSubalgebraMeasureAlgebraIso
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (T : BooleanSubalgebra (PositiveFragmentAlgebra f))
    (hT : IsClosed (T : Set (PositiveFragmentAlgebra f)))
    (φ : S ≃o T)
    (hφ : ∀ a : S, ‖positiveFragmentValue (φ a).val‖ = ‖positiveFragmentValue a.val‖) :
    @MeasureAlgebraIso _ (booleanSubalgebraStoneMeasurableSpace S)
      _ (booleanSubalgebraStoneMeasurableSpace T)
      (alSubalgebraMeasure hE e S) (alSubalgebraMeasure hF f T) := by
  letI := booleanSubalgebraStoneMeasurableSpace S
  letI := booleanSubalgebraStoneMeasurableSpace T
  let eS := alSubalgebraMeasureAlgebraEquiv hE e S hS
  let eT := alSubalgebraMeasureAlgebraEquiv hF f T hT
  let ψ := eS.symm.trans (φ.toEquiv.trans eT)
  have hψ (a : S) : ψ (alSubalgebraClass hE e S a) = alSubalgebraClass hF f T (φ a) := by
    change eT (φ (eS.symm (eS a))) = eT (φ a)
    rw [Equiv.symm_apply_apply]
  refine { toEquiv := ψ, map_compl := ?_, map_iUnion := ?_, measure_eq := ?_ }
  · intro c
    obtain ⟨a, rfl⟩ := alSubalgebraClass_surjective hE e S hS c
    rw [← alSubalgebraClass_compl, hψ, hψ, ← alSubalgebraClass_compl]
    exact congrArg _ (map_compl' φ a)
  · intro ι _ c
    let a : ι → S := fun i => eS.symm (c i)
    let b : S := eS.symm (MeasureAlgebra.iUnion c)
    have ha (i : ι) : alSubalgebraClass hE e S (a i) = c i := eS.apply_symm_apply _
    have hb : alSubalgebraClass hE e S b = MeasureAlgebra.iUnion c := eS.apply_symm_apply _
    have hba : IsLUB (Set.range a) b := by
      apply (alSubalgebraClass_iUnion_iff_isLUB hE e S hS a b).mp
      simpa only [ha] using hb
    have hφba : IsLUB (Set.range (fun i => φ (a i))) (φ b) := by
      constructor
      · rintro _ ⟨i, rfl⟩
        exact φ.monotone (hba.1 (Set.mem_range_self i))
      · intro d hd
        apply φ.le_symm_apply.mp
        apply hba.2
        rintro _ ⟨i, rfl⟩
        exact φ.le_symm_apply.mpr (hd (Set.mem_range_self i))
    calc
      ψ (MeasureAlgebra.iUnion c) = alSubalgebraClass hF f T (φ b) := by rw [← hb, hψ]
      _ = MeasureAlgebra.iUnion (fun i => alSubalgebraClass hF f T (φ (a i))) :=
        (alSubalgebraClass_iUnion_iff_isLUB hF f T hT _ _).mpr hφba
      _ = MeasureAlgebra.iUnion (fun i => ψ (c i)) := rfl
  · intro c
    obtain ⟨a, rfl⟩ := alSubalgebraClass_surjective hE e S hS c
    rw [hψ, measure_alSubalgebraClass, measure_alSubalgebraClass, hφ]

theorem alSubalgebraMeasureAlgebraIso_class
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (T : BooleanSubalgebra (PositiveFragmentAlgebra f))
    (hT : IsClosed (T : Set (PositiveFragmentAlgebra f)))
    (φ : S ≃o T)
    (hφ : ∀ a : S, ‖positiveFragmentValue (φ a).val‖ = ‖positiveFragmentValue a.val‖)
    (a : S) :
    letI := booleanSubalgebraStoneMeasurableSpace S
    letI := booleanSubalgebraStoneMeasurableSpace T
    (alSubalgebraMeasureAlgebraIso hE e hF f S hS T hT φ hφ).toEquiv
        (alSubalgebraClass hE e S a) = alSubalgebraClass hF f T (φ a) := by
  change (alSubalgebraMeasureAlgebraEquiv hF f T hT)
    (φ ((alSubalgebraMeasureAlgebraEquiv hE e S hS).symm
      ((alSubalgebraMeasureAlgebraEquiv hE e S hS) a))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end ThesisCommon


