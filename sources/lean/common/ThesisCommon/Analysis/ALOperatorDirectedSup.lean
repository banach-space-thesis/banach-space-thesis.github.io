import ThesisCommon.Analysis.PositiveOperatorOrder
import ThesisCommon.Analysis.PositiveConeExtension
import ThesisCommon.Analysis.ALOrderCompleteness

/-! Directed suprema of positive bounded operators with an AL range.
The supremum is constructed pointwise on positive inputs, its additivity
is proved by directedness, and its norm bound gives an actual bounded map. -/
noncomputable section
open Set Filter Topology
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice F]
variable [IsOrderedAddMonoid F] [HasSolidNorm F] [CompleteSpace F] [OrderClosedTopology F]
variable (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
variable {s : Set (E →L[ℝ] F)} (hs : s.Nonempty) (hpos : ∀ T ∈ s, 0 ≤ T)
variable (hdir : DirectedOn (· ≤ ·) s) (R : E →L[ℝ] F) (hR : ∀ T ∈ s, T ≤ R)

include hALF hs hpos hdir hR in
omit [HasSolidNorm E] in
theorem exists_operatorDirectedSup_value (x : E) (hx : 0 ≤ x) :
    ∃ y : F, IsLUB ((fun T : E →L[ℝ] F => T x) '' s) y ∧ 0 ≤ y ∧ ‖y‖ ≤ ‖R‖ * ‖x‖ := by
  have hvalpos : ∀ y ∈ (fun T : E →L[ℝ] F => T x) '' s, 0 ≤ y := by
    rintro _ ⟨T, hT, rfl⟩
    exact hpos T hT x hx
  have hvaldir : DirectedOn (· ≤ ·) ((fun T : E →L[ℝ] F => T x) '' s) := by
    rintro _ ⟨T, hT, rfl⟩ _ ⟨U, hU, rfl⟩
    obtain ⟨V, hV, hTV, hUV⟩ := hdir T hT U hU
    exact ⟨V x, ⟨V, hV, rfl⟩, hTV x hx, hUV x hx⟩
  have hnorm (T : E →L[ℝ] F) (hT : T ∈ s) : ‖T x‖ ≤ ‖R‖ * ‖x‖ := by
    have hTx : 0 ≤ T x := hpos T hT x hx
    have hTR : T x ≤ R x := hR T hT x hx
    have hnorm : ‖T x‖ ≤ ‖R x‖ := norm_le_norm_of_abs_le_abs (by
      simpa only [abs_of_nonneg hTx, abs_of_nonneg (hTx.trans hTR)] using hTR)
    exact hnorm.trans (R.le_opNorm x)
  have hbdd : BddAbove (norm '' ((fun T : E →L[ℝ] F => T x) '' s)) := by
    refine ⟨‖R‖ * ‖x‖, ?_⟩
    rintro _ ⟨_, ⟨T, hT, rfl⟩, rfl⟩
    exact hnorm T hT
  obtain ⟨y, hy, _, _, _, _⟩ := al_exists_isLUB_of_directed_norm_bdd hALF
    (hs.image (fun T => T x)) hvalpos hvaldir hbdd
  obtain ⟨T, hT⟩ := hs
  have hypos : 0 ≤ y := (hpos T hT x hx).trans (hy.1 ⟨T, hT, rfl⟩)
  have hyR : y ≤ R x := hy.2 (by rintro _ ⟨U, hU, rfl⟩; exact hR U hU x hx)
  refine ⟨y, hy, hypos, ?_⟩
  exact (norm_le_norm_of_abs_le_abs (by
    simpa only [abs_of_nonneg hypos, abs_of_nonneg (hypos.trans hyR)] using hyR)).trans (R.le_opNorm x)

def operatorDirectedSupPos (x : E) (hx : 0 ≤ x) : F :=
  (exists_operatorDirectedSup_value hALF hs hpos hdir R hR x hx).choose

omit [HasSolidNorm E] in
theorem operatorDirectedSupPos_isLUB (x : E) (hx : 0 ≤ x) :
    IsLUB ((fun T : E →L[ℝ] F => T x) '' s) (operatorDirectedSupPos hALF hs hpos hdir R hR x hx) :=
  (exists_operatorDirectedSup_value hALF hs hpos hdir R hR x hx).choose_spec.1

omit [HasSolidNorm E] in
theorem operatorDirectedSupPos_nonneg (x : E) (hx : 0 ≤ x) :
    0 ≤ operatorDirectedSupPos hALF hs hpos hdir R hR x hx :=
  (exists_operatorDirectedSup_value hALF hs hpos hdir R hR x hx).choose_spec.2.1

omit [HasSolidNorm E] in
theorem norm_operatorDirectedSupPos_le (x : E) (hx : 0 ≤ x) :
    ‖operatorDirectedSupPos hALF hs hpos hdir R hR x hx‖ ≤ ‖R‖ * ‖x‖ :=
  (exists_operatorDirectedSup_value hALF hs hpos hdir R hR x hx).choose_spec.2.2

omit [HasSolidNorm E] in
theorem operatorDirectedSupPos_add (x y : E) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    operatorDirectedSupPos hALF hs hpos hdir R hR (x + y) (add_nonneg hx hy) =
      operatorDirectedSupPos hALF hs hpos hdir R hR x hx + operatorDirectedSupPos hALF hs hpos hdir R hR y hy := by
  let P := operatorDirectedSupPos hALF hs hpos hdir R hR
  have hPx := operatorDirectedSupPos_isLUB hALF hs hpos hdir R hR x hx
  have hPy := operatorDirectedSupPos_isLUB hALF hs hpos hdir R hR y hy
  have hPxy := operatorDirectedSupPos_isLUB hALF hs hpos hdir R hR (x + y) (add_nonneg hx hy)
  apply le_antisymm
  · apply hPxy.2
    rintro _ ⟨T, hT, rfl⟩
    dsimp only
    rw [map_add]
    exact add_le_add (hPx.1 ⟨T, hT, rfl⟩) (hPy.1 ⟨T, hT, rfl⟩)
  · have hinner (U : E →L[ℝ] F) (hU : U ∈ s) : P x hx + U y ≤ P (x + y) (add_nonneg hx hy) := by
      apply le_sub_iff_add_le.mp
      apply hPx.2
      rintro _ ⟨T, hT, rfl⟩
      apply le_sub_iff_add_le.mpr
      obtain ⟨V, hV, hTV, hUV⟩ := hdir T hT U hU
      exact (add_le_add (hTV x hx) (hUV y hy)).trans (by
        rw [← map_add]
        exact hPxy.1 ⟨V, hV, rfl⟩)
    apply le_sub_iff_add_le'.mp
    apply hPy.2
    rintro _ ⟨U, hU, rfl⟩
    exact le_sub_iff_add_le'.mpr (hinner U hU)

def operatorDirectedSup : E →L[ℝ] F :=
  positiveConeExtension (operatorDirectedSupPos hALF hs hpos hdir R hR)
    (operatorDirectedSupPos_add hALF hs hpos hdir R hR) (norm_nonneg R)
    (norm_operatorDirectedSupPos_le hALF hs hpos hdir R hR)

theorem operatorDirectedSup_apply_of_nonneg (x : E) (hx : 0 ≤ x) :
    operatorDirectedSup hALF hs hpos hdir R hR x = operatorDirectedSupPos hALF hs hpos hdir R hR x hx :=
  positiveConeExtension_apply_of_nonneg _ _ _ _ x hx

theorem operatorDirectedSup_isLUB : IsLUB s (operatorDirectedSup hALF hs hpos hdir R hR) := by
  constructor
  · intro T hT x hx
    rw [operatorDirectedSup_apply_of_nonneg hALF hs hpos hdir R hR x hx]
    exact (operatorDirectedSupPos_isLUB hALF hs hpos hdir R hR x hx).1 ⟨T, hT, rfl⟩
  · intro U hU x hx
    rw [operatorDirectedSup_apply_of_nonneg hALF hs hpos hdir R hR x hx]
    apply (operatorDirectedSupPos_isLUB hALF hs hpos hdir R hR x hx).2
    rintro _ ⟨T, hT, rfl⟩
    exact hU hT x hx

theorem operatorDirectedSup_apply_isLUB (x : E) (hx : 0 ≤ x) :
    IsLUB ((fun T : E →L[ℝ] F => T x) '' s) (operatorDirectedSup hALF hs hpos hdir R hR x) := by
  rw [operatorDirectedSup_apply_of_nonneg hALF hs hpos hdir R hR x hx]
  exact operatorDirectedSupPos_isLUB hALF hs hpos hdir R hR x hx

include hALF hs hpos hdir in
theorem operator_isLUB_apply_of_directed {S : E →L[ℝ] F} (hS : IsLUB s S)
    (x : E) (hx : 0 ≤ x) : IsLUB ((fun T : E →L[ℝ] F => T x) '' s) (S x) := by
  have heq := (operatorDirectedSup_isLUB hALF hs hpos hdir S (fun _ hT => hS.1 hT)).unique hS
  rw [← heq]
  exact operatorDirectedSup_apply_isLUB hALF hs hpos hdir S (fun _ hT => hS.1 hT) x hx

end ThesisCommon
