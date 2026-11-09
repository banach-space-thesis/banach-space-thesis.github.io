import PEMS.Section44BandCuts
import PEMS.StrictlyLocalizableOperators

/-! An arbitrary choice of the finite domain pieces and σ-finite range supports
from §4.4. The global operators are the sums of their indicated restrictions. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal Function Classical ThesisCommon.PositiveOperatorOrder

namespace PEMS
set_option maxHeartbeats 400000

variable {I X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

structure Section44Partition (I : Type*) (μ : Measure X) where
  piece : I → Set X
  measurable : ∀ i, MeasurableSet (piece i)
  finite : ∀ i, μ (piece i) < ⊤
  disjoint : Pairwise (Disjoint on piece)
  covers : (⋃ i, piece i) = univ
  measurable_of_pieces : ∀ A : Set X, (∀ i, MeasurableSet (A ∩ piece i)) → MeasurableSet A
  sum_restrict : Measure.sum (fun i => μ.restrict (piece i)) = μ

namespace Section44Partition

variable (D : Section44Partition I μ)

instance finitePiece (i : I) : IsFiniteMeasure (μ.restrict (D.piece i)) :=
  isFiniteMeasure_restrict.mpr (D.finite i).ne

def includePiece (i : I) : LOne ℝ (μ.restrict (D.piece i)) →L[ℝ] LOne ℝ μ :=
  (lebesgueLpExtend (𝕜 := ℝ) (D.piece i) (D.measurable i)).toContinuousLinearMap

theorem norm_includePiece_le (i : I) : ‖D.includePiece i‖ ≤ 1 :=
  (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := μ)
    (D.piece i) (D.measurable i)).norm_toContinuousLinearMap_le

def paste (f : I → X → ℝ) (x : X) : ℝ :=
  f (show ∃ i, x ∈ D.piece i from mem_iUnion.mp (D.covers ▸ mem_univ x)).choose x

theorem paste_eq (f : I → X → ℝ) {x : X} {i : I} (hx : x ∈ D.piece i) :
    D.paste f x = f i x := by
  let h : ∃ j, x ∈ D.piece j := mem_iUnion.mp (D.covers ▸ mem_univ x)
  have heq : h.choose = i := by
    by_contra hne
    exact Set.disjoint_left.mp (D.disjoint hne) h.choose_spec hx
  change f h.choose x = f i x
  rw [heq]

theorem measurable_paste (f : I → X → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (D.paste f) := by
  intro A hA
  apply D.measurable_of_pieces
  intro i
  have heq : D.paste f ⁻¹' A ∩ D.piece i = f i ⁻¹' A ∩ D.piece i := by
    ext x
    constructor <;> rintro ⟨hx, hi⟩ <;> refine ⟨?_, hi⟩
    · change D.paste f x ∈ A at hx
      change f i x ∈ A
      rwa [D.paste_eq f hi] at hx
    · change f i x ∈ A at hx
      change D.paste f x ∈ A
      rwa [D.paste_eq f hi]
  rw [heq]
  exact ((hf i) hA).inter (D.measurable i)

theorem norm_comp_piece_le (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (i : I) :
    ‖T.comp (D.includePiece i)‖ ≤ ‖T‖ :=
  (T.opNorm_comp_le (D.includePiece i)).trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (D.norm_includePiece_le i) (norm_nonneg T))

theorem norm_le_iff_pieces (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) {c : ℝ} (hc : 0 ≤ c) :
    ‖T‖ ≤ c ↔ ∀ i, ‖T.comp (D.includePiece i)‖ ≤ c := by
  exact ⟨fun h i => (D.norm_comp_piece_le T i).trans h, fun h =>
    decomposableL1Operator_norm_le_of_pieces D.piece D.measurable D.disjoint D.sum_restrict T c hc h⟩

end Section44Partition

structure Section44Decomposition (I : Type*) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) where
  partition : Section44Partition I μ
  support : I → Set Y
  measurable_support : ∀ i, MeasurableSet (support i)
  sigmaFinite_support : ∀ i, SigmaFinite (ν.restrict (support i))
  singularPart : ∀ i, LOne ℝ (μ.restrict (partition.piece i)) →L[ℝ] LOne ℝ (ν.restrict (support i))
  integralPart : ∀ i, LOne ℝ (μ.restrict (partition.piece i)) →L[ℝ] LOne ℝ (ν.restrict (support i))
  kernel : I → X × Y → ℝ
  singular : ∀ i, IsSingularOperator (singularPart i)
  represents : ∀ i, IsIntegralKernel (kernel i) (integralPart i)
  kernel_zero_off : ∀ i x y, y ∉ support i → kernel i (x, y) = 0
  decompose : ∀ i, T.comp (partition.includePiece i) =
    (lebesgueLpExtend (𝕜 := ℝ) (support i) (measurable_support i)).toContinuousLinearMap.comp
      (singularPart i + integralPart i)

namespace Section44Decomposition

variable {T : LOne ℝ μ →L[ℝ] LOne ℝ ν} (D : Section44Decomposition I T)

def outputExtend (i : I) : LOne ℝ (ν.restrict (D.support i)) →L[ℝ] LOne ℝ ν :=
  (lebesgueLpExtend (𝕜 := ℝ) (D.support i) (D.measurable_support i)).toContinuousLinearMap

theorem norm_local_le (i : I) : ‖D.singularPart i + D.integralPart i‖ ≤ ‖T‖ := by
  have heq : (lebesgueLpRestrict (𝕜 := ℝ) (D.support i)).comp
      (T.comp (D.partition.includePiece i)) = D.singularPart i + D.integralPart i := by
    rw [D.decompose i]
    ext f : 1
    exact lebesgueLpRestrict_extend (𝕜 := ℝ) (D.support i) (D.measurable_support i)
      ((D.singularPart i + D.integralPart i) f)
  rw [← heq]
  calc
    _ ≤ ‖lebesgueLpRestrict (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := ν) (D.support i)‖ *
        ‖T.comp (D.partition.includePiece i)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T.comp (D.partition.includePiece i)‖ :=
      mul_le_mul_of_nonneg_right
        (norm_lebesgueLpRestrict_le (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := ν) (D.support i))
        (norm_nonneg _)
    _ ≤ ‖T‖ := by rw [one_mul]; exact D.partition.norm_comp_piece_le T i

theorem abs_local (i : I) : |D.singularPart i + D.integralPart i| =
    |D.singularPart i| + |D.integralPart i| := by
  letI := D.partition.finitePiece i
  letI := D.sigmaFinite_support i
  exact singular_integral_abs_add (D.singular i) ⟨_, D.represents i⟩

theorem norm_singular_le (i : I) : ‖D.singularPart i‖ ≤ ‖T‖ := by
  apply le_trans _ (D.norm_local_le i)
  apply norm_le_norm_of_abs_le_abs
  rw [D.abs_local i]
  exact le_add_of_nonneg_right (abs_nonneg _)

theorem norm_integral_le (i : I) : ‖D.integralPart i‖ ≤ ‖T‖ := by
  apply le_trans _ (D.norm_local_le i)
  apply norm_le_norm_of_abs_le_abs
  rw [D.abs_local i]
  exact le_add_of_nonneg_left (abs_nonneg _)

theorem norm_outputExtend_comp_le (i : I)
    (A : LOne ℝ (μ.restrict (D.partition.piece i)) →L[ℝ] LOne ℝ (ν.restrict (D.support i))) :
    ‖(D.outputExtend i).comp A‖ ≤ ‖A‖ := by
  have h : ‖D.outputExtend i‖ ≤ 1 :=
    (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := ν)
      (D.support i) (D.measurable_support i)).norm_toContinuousLinearMap_le
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right h (norm_nonneg A)).trans_eq (one_mul _))

def assemble
    (A : ∀ i, LOne ℝ (μ.restrict (D.partition.piece i)) →L[ℝ] LOne ℝ (ν.restrict (D.support i)))
    (hA : ∀ i, ‖A i‖ ≤ ‖T‖) : LOne ℝ μ →L[ℝ] LOne ℝ ν :=
  decomposableL1Operator D.partition.piece D.partition.sum_restrict
    (fun i => (D.outputExtend i).comp (A i)) ‖T‖ (norm_nonneg T)
    (fun i => (D.norm_outputExtend_comp_le i (A i)).trans (hA i))

theorem assemble_comp
    (A : ∀ i, LOne ℝ (μ.restrict (D.partition.piece i)) →L[ℝ] LOne ℝ (ν.restrict (D.support i)))
    (hA : ∀ i, ‖A i‖ ≤ ‖T‖) (i : I) :
    (D.assemble A hA).comp (D.partition.includePiece i) = (D.outputExtend i).comp (A i) := by
  ext f : 1
  exact decomposableL1Operator_extend D.partition.piece D.partition.measurable
    D.partition.disjoint D.partition.sum_restrict (fun j => (D.outputExtend j).comp (A j))
    ‖T‖ (norm_nonneg T) (fun j => (D.norm_outputExtend_comp_le j (A j)).trans (hA j)) i f

def S : LOne ℝ μ →L[ℝ] LOne ℝ ν := D.assemble D.singularPart D.norm_singular_le
def K : LOne ℝ μ →L[ℝ] LOne ℝ ν := D.assemble D.integralPart D.norm_integral_le

theorem decomposition_eq : T = D.S + D.K := by
  let A := fun i => T.comp (D.partition.includePiece i)
  let hA := D.partition.norm_comp_piece_le T
  refine (decomposableL1Operator_unique D.partition.piece D.partition.measurable D.partition.disjoint
    D.partition.sum_restrict A ‖T‖ (norm_nonneg T) hA T (fun _ => rfl)).trans ?_
  symm
  apply decomposableL1Operator_unique D.partition.piece D.partition.measurable D.partition.disjoint
    D.partition.sum_restrict A ‖T‖ (norm_nonneg T) hA
  intro i
  calc
    _ = D.S.comp (D.partition.includePiece i) + D.K.comp (D.partition.includePiece i) :=
      ContinuousLinearMap.add_comp _ _ _
    _ = (D.outputExtend i).comp (D.singularPart i) + (D.outputExtend i).comp (D.integralPart i) :=
      congrArg₂ (· + ·) (D.assemble_comp _ _ i) (D.assemble_comp _ _ i)
    _ = (D.outputExtend i).comp (D.singularPart i + D.integralPart i) :=
      (ContinuousLinearMap.comp_add _ _ _).symm
    _ = _ := (D.decompose i).symm

def gluedKernel (x : X) (y : Y) : ℝ := D.partition.paste (fun i z => D.kernel i (z, y)) x

theorem gluedKernel_eq {x : X} {i : I} (hx : x ∈ D.partition.piece i) (y : Y) :
    D.gluedKernel x y = D.kernel i (x, y) :=
  D.partition.paste_eq _ hx

theorem abs_piece (i : I) :
    |T|.comp (D.partition.includePiece i) =
      (D.outputExtend i).comp (|D.singularPart i| + |D.integralPart i|) := by
  calc
    _ = |T.comp (D.partition.includePiece i)| :=
      (section44_abs_comp_extend (D.partition.piece i) (D.partition.measurable i) T).symm
    _ = |(D.outputExtend i).comp (D.singularPart i + D.integralPart i)| :=
      congrArg abs (D.decompose i)
    _ = (D.outputExtend i).comp |D.singularPart i + D.integralPart i| :=
      section44_abs_extend_comp (D.support i) (D.measurable_support i) _
    _ = _ := congrArg ((D.outputExtend i).comp ·) (D.abs_local i)

end Section44Decomposition
end PEMS
