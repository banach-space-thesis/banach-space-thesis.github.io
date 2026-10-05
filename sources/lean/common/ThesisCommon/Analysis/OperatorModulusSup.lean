import ThesisCommon.Analysis.ALOrderCompleteness
import ThesisCommon.Analysis.RieszDecomposition
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! The Riesz--Kantorovich supremum for bounded operators between real AL-spaces.
Finite decompositions are actual positive pieces of the input vector. Their
image-modulus sums form a directed family with a proved uniform norm bound. -/
noncomputable section
open Set Filter Topology Finset
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [Lattice F] [IsOrderedAddMonoid F] [HasSolidNorm F]

/-- A finite positive decomposition of an actual vector. -/
structure PositiveDecomposition (x : E) where
  Index : Type
  [finite : Fintype Index]
  part : Index → E
  nonneg : ∀ i, 0 ≤ part i
  sum_eq : ∑ i, part i = x

attribute [instance] PositiveDecomposition.finite

namespace PositiveDecomposition

def single (x : E) (hx : 0 ≤ x) : PositiveDecomposition x where
  Index := Unit
  part := fun _ => x
  nonneg := fun _ => hx
  sum_eq := by simp

def value (T : E →L[ℝ] F) {x : E} (d : PositiveDecomposition x) : F :=
  ∑ i, |T (d.part i)|

def append {x y : E} (d : PositiveDecomposition x) (e : PositiveDecomposition y) :
    PositiveDecomposition (x + y) where
  Index := d.Index ⊕ e.Index
  part := Sum.elim d.part e.part
  nonneg := by intro i; cases i with
    | inl i => exact d.nonneg i
    | inr j => exact e.nonneg j
  sum_eq := by simp [Fintype.sum_sum_type, d.sum_eq, e.sum_eq]

omit [IsOrderedAddMonoid E] [HasSolidNorm E] [IsOrderedAddMonoid F] [HasSolidNorm F] in
theorem value_append (T : E →L[ℝ] F) {x y : E}
    (d : PositiveDecomposition x) (e : PositiveDecomposition y) :
    (d.append e).value T = d.value T + e.value T := by
  simp [value, append, Fintype.sum_sum_type]

omit [HasSolidNorm E] [HasSolidNorm F] in
/-- Split a decomposition of x+y into decompositions of x and y. The triangle
inequality for the lattice modulus bounds the original image sum. -/
theorem exists_split_value (T : E →L[ℝ] F) {x y : E} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (d : PositiveDecomposition (x + y)) :
    ∃ a : PositiveDecomposition x, ∃ b : PositiveDecomposition y,
      d.value T ≤ a.value T + b.value T := by
  obtain ⟨u, hu, husum⟩ := riesz_split_finset univ d.part (fun i _ => d.nonneg i) x hx
    (by rw [d.sum_eq]; exact le_add_of_nonneg_right hy)
  let a : PositiveDecomposition x :=
    { Index := d.Index, part := u, nonneg := fun i => (hu i (mem_univ _)).1, sum_eq := husum }
  let b : PositiveDecomposition y :=
    { Index := d.Index
      part := fun i => d.part i - u i
      nonneg := fun i => sub_nonneg.mpr (hu i (mem_univ _)).2
      sum_eq := by rw [sum_sub_distrib, d.sum_eq, husum]; abel }
  refine ⟨a, b, ?_⟩
  change (∑ i, |T (d.part i)|) ≤ (∑ i, |T (u i)|) + ∑ i, |T (d.part i - u i)|
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro i _
  have heq : d.part i = u i + (d.part i - u i) := by abel
  conv_lhs => rw [heq, map_add]
  exact abs_add_le _ _

omit [IsOrderedAddMonoid E] [HasSolidNorm E] [HasSolidNorm F] in
theorem value_nonneg (T : E →L[ℝ] F) {x : E} (d : PositiveDecomposition x) :
    0 ≤ d.value T := sum_nonneg fun _ _ => abs_nonneg _

omit [IsOrderedAddMonoid E] [HasSolidNorm E] [IsOrderedAddMonoid F] [HasSolidNorm F] in
theorem value_single (T : E →L[ℝ] F) (x : E) (hx : 0 ≤ x) :
    (single x hx).value T = |T x| := by simp [value, single]

omit [HasSolidNorm E] [HasSolidNorm F] in
/-- A common positive refinement increases both image-modulus sums. -/
theorem exists_value_ge_pair (T : E →L[ℝ] F) {x : E} (d e : PositiveDecomposition x) :
    ∃ q : PositiveDecomposition x, d.value T ≤ q.value T ∧ e.value T ≤ q.value T := by
  obtain ⟨c, hc, hrows, hcols⟩ := riesz_refine_finsets univ univ d.part e.part
    (fun i _ => d.nonneg i) (fun j _ => e.nonneg j) (d.sum_eq.trans e.sum_eq.symm)
  let q : PositiveDecomposition x :=
    { Index := d.Index × e.Index
      part := fun z => c z.1 z.2
      nonneg := fun z => hc z.1 (mem_univ _) z.2 (mem_univ _)
      sum_eq := by
        rw [Fintype.sum_prod_type]
        simp_rw [hrows _ (mem_univ _)]
        exact d.sum_eq }
  refine ⟨q, ?_, ?_⟩
  · calc
      d.value T ≤ ∑ i, ∑ j, |T (c i j)| := by
        apply sum_le_sum
        intro i _
        rw [← hrows i (mem_univ _), map_sum]
        exact lattice_abs_sum_le _ _
      _ = q.value T := by simp only [value, q, Fintype.sum_prod_type]
  · calc
      e.value T ≤ ∑ j, ∑ i, |T (c i j)| := by
        apply sum_le_sum
        intro j _
        rw [← hcols j (mem_univ _), map_sum]
        exact lattice_abs_sum_le _ _
      _ = q.value T := by rw [sum_comm]; simp only [value, q, Fintype.sum_prod_type]

omit [HasSolidNorm E] in
theorem norm_value_le (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (T : E →L[ℝ] F) {x : E} (d : PositiveDecomposition x) :
    ‖d.value T‖ ≤ ‖T‖ * ‖x‖ := by
  calc
    ‖d.value T‖ ≤ ∑ i, ‖|T (d.part i)|‖ := norm_sum_le _ _
    _ = ∑ i, ‖T (d.part i)‖ := by simp only [norm_abs_eq_norm]
    _ ≤ ∑ i, ‖T‖ * ‖d.part i‖ := sum_le_sum fun i _ => T.le_opNorm _
    _ = ‖T‖ * ‖x‖ := by
      rw [← mul_sum, ← al_norm_sum hALE univ d.part (fun i _ => d.nonneg i), d.sum_eq]

end PositiveDecomposition

def modulusCandidates (T : E →L[ℝ] F) (x : E) : Set F :=
  range (fun d : PositiveDecomposition x => d.value T)

omit [HasSolidNorm E] [HasSolidNorm F] in
theorem modulusCandidates_directed (T : E →L[ℝ] F) (x : E) :
    DirectedOn (· ≤ ·) (modulusCandidates T x) := by
  rintro _ ⟨d, rfl⟩ _ ⟨e, rfl⟩
  obtain ⟨q, hd, he⟩ := d.exists_value_ge_pair T e
  exact ⟨q.value T, ⟨q, rfl⟩, hd, he⟩

variable [CompleteSpace F] [OrderClosedTopology F]

omit [HasSolidNorm E] in
/-- Existence of the actual modulus value on a positive input, with the sharp
operator-norm bound. OperatorModulus extends these values to the whole lattice. -/
theorem exists_operatorModulus_value
    (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (T : E →L[ℝ] F) (x : E) (hx : 0 ≤ x) :
    ∃ y : F, IsLUB (modulusCandidates T x) y ∧ 0 ≤ y ∧ ‖y‖ ≤ ‖T‖ * ‖x‖ := by
  have hne : (modulusCandidates T x).Nonempty :=
    ⟨(PositiveDecomposition.single x hx).value T, ⟨_, rfl⟩⟩
  have hpos : ∀ z ∈ modulusCandidates T x, 0 ≤ z := by
    rintro _ ⟨d, rfl⟩
    exact d.value_nonneg T
  have hbound : BddAbove (norm '' modulusCandidates T x) := by
    refine ⟨‖T‖ * ‖x‖, ?_⟩
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    exact d.norm_value_le hALE T
  obtain ⟨y, hlub, u, hu, hulim, _⟩ :=
    al_exists_isLUB_of_directed_norm_bdd hALF hne hpos (modulusCandidates_directed T x) hbound
  refine ⟨y, hlub, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hne
    exact (hpos z hz).trans (hlub.1 hz)
  · apply le_of_tendsto' (hulim.norm)
    intro n
    obtain ⟨d, hd⟩ := hu n
    rw [← hd]
    exact d.norm_value_le hALE T

end ThesisCommon
