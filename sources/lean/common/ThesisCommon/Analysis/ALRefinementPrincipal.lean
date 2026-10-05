import ThesisCommon.Analysis.ALFragmentBasic
import ThesisCommon.Analysis.ALRenormPartition
import ThesisCommon.Analysis.BandProjectionModulus

/-! Actual principal bands and their contractive projections in a Dedekind
complete real normed lattice. No AL norm assumption is used. -/
noncomputable section
open Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
  [IsOrderedModule ℝ E] [HasSolidNorm E]

def latticeDisjointComplement (S : Set E) : Submodule ℝ E where
  carrier := {x | ∀ y ∈ S, |x| ⊓ |y| = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x z hx hz y hy
    have hsum : (|x|+|z|) ⊓ |y| = 0 := by
      rw [inf_comm]
      exact positive_inf_add_eq_zero (abs_nonneg y) (abs_nonneg x) (abs_nonneg z)
        (by rw [inf_comm]; exact hx y hy) (by rw [inf_comm]; exact hz y hy)
    exact le_antisymm ((inf_le_inf_right _ (abs_add_le x z)).trans_eq hsum)
      (le_inf (abs_nonneg _) (abs_nonneg _))
  smul_mem' := by
    intro r x hx y hy
    obtain ⟨n,hn⟩ := exists_nat_ge |r|
    have hbound : |r • x| ≤ n • |x| := by
      rw [al_lattice_abs_smul, ← Nat.cast_smul_eq_nsmul ℝ]
      exact smul_le_smul_of_nonneg_right hn (abs_nonneg x)
    exact eq_zero_of_le_nsmul_of_inf_eq_zero (abs_nonneg x) (hx y hy) n
      (le_inf (abs_nonneg _) (abs_nonneg _)) (inf_le_left.trans hbound) inf_le_right

@[simp] theorem mem_latticeDisjointComplement (S : Set E) (x : E) :
    x ∈ latticeDisjointComplement S ↔ ∀ y ∈ S, |x| ⊓ |y| = 0 := Iff.rfl

private theorem disjoint_of_isLUB {s : Set E} {x y : E}
    (hs : s.Nonempty) (hpos : ∀ z ∈ s, 0 ≤ z) (hx : IsLUB s x) (hy : 0 ≤ y)
    (hdisj : ∀ z ∈ s, z ⊓ y = 0) : x ⊓ y = 0 := by
  obtain ⟨z,hz⟩ := hs
  have hx0 : 0 ≤ x := (hpos z hz).trans (hx.1 hz)
  have hsum : x+y ≤ x ⊔ y := by
    apply le_sub_iff_add_le.mp
    apply hx.2
    intro u hu
    apply le_sub_iff_add_le.mpr
    have heq : u+y = u ⊔ y := by
      simpa only [hdisj u hu, zero_add] using (inf_add_sup u y).symm
    rw [heq]
    exact sup_le_sup_right (hx.1 hu) y
  have hle : (x ⊓ y)+(x ⊔ y) ≤ x ⊔ y := by rw [inf_add_sup]; exact hsum
  exact le_antisymm (by simpa using hle) (le_inf hx0 hy)

theorem latticeDisjointComplement_orderClosed (S : Set E) :
    IsOrderClosedIdeal (latticeDisjointComplement S) where
  solid := by
    intro x y hy hxy z hz
    exact le_antisymm ((inf_le_inf_right _ hxy).trans_eq (hy z hz))
      (le_inf (abs_nonneg _) (abs_nonneg _))
  closed := by
    intro s hs hmem hpos _ x hx z hz
    obtain ⟨w,hw⟩ := hs
    have hx0 : 0 ≤ x := (hpos w hw).trans (hx.1 hw)
    rw [abs_of_nonneg hx0]
    apply disjoint_of_isLUB ⟨w,hw⟩ hpos hx (abs_nonneg z)
    intro y hy
    have h := hmem y hy z hz
    rwa [abs_of_nonneg (hpos y hy)] at h

def principalBand (a : E) : Submodule ℝ E :=
  latticeDisjointComplement (latticeDisjointComplement {a} : Set E)

theorem principalBand_orderClosed (a : E) : IsOrderClosedIdeal (principalBand a) :=
  latticeDisjointComplement_orderClosed _

theorem self_mem_principalBand (a : E) : a ∈ principalBand a := by
  intro y hy
  rw [inf_comm]
  exact hy a (Set.mem_singleton a)

def principalBandProjection (a : E) : E →L[ℝ] E :=
  bandProjection (principalBand_orderClosed a)

theorem principalBandProjection_nonneg (a : E) : 0 ≤ principalBandProjection a :=
  (principalBand_orderClosed a).bandProjection_nonneg

theorem principalBandProjection_le_id (a : E) :
    principalBandProjection a ≤ ContinuousLinearMap.id ℝ E :=
  (principalBand_orderClosed a).bandProjection_le_id

theorem principalBandProjection_self (a : E) : principalBandProjection a a = a :=
  (principalBand_orderClosed a).bandProjection_eq_self (self_mem_principalBand a)

theorem principalBandProjection_idempotent (a x : E) :
    principalBandProjection a (principalBandProjection a x) = principalBandProjection a x :=
  (principalBand_orderClosed a).bandProjection_idempotent x

theorem principalBandProjection_eq_zero_iff (a x : E) :
    principalBandProjection a x = 0 ↔ |x| ⊓ |a| = 0 := by
  constructor
  · intro h
    exact ((principalBand_orderClosed a).bandProjection_eq_zero_iff x).mp h a
      (self_mem_principalBand a)
  · intro h
    apply ((principalBand_orderClosed a).bandProjection_eq_zero_iff x).mpr
    intro y hy
    rw [inf_comm]
    apply hy x
    intro z hz
    have hza : z = a := hz
    simpa only [hza] using h

theorem principalBandProjection_abs (a x : E) :
    principalBandProjection a |x| = |principalBandProjection a x| :=
  (principalBand_orderClosed a).bandProjection_abs x

theorem norm_principalBandProjection_le_one (a : E) : ‖principalBandProjection a‖ ≤ 1 :=
  (principalBand_orderClosed a).norm_bandProjection_le_one

end ThesisCommon
