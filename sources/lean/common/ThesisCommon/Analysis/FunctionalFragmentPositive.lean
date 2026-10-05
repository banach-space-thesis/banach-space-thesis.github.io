import ThesisCommon.Analysis.PositiveOperatorOrder
import ThesisCommon.Analysis.PositiveConeExtension
import ThesisCommon.Analysis.RieszDecomposition
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! The fragment of a positive functional carried by the principal ideal of
a positive vector. Suprema are taken in the real scalars; the domain lattice
need not be Dedekind complete or have band projections. -/
noncomputable section
namespace ThesisCommon
open scoped PositiveOperatorOrder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E]

def principalPositiveBelow (a x : E) : Set E :=
  {y | 0 ≤ y ∧ y ≤ x ∧ ∃ n : ℕ, y ≤ n • a}

def functionalFragmentValues (φ : E →L[ℝ] ℝ) (a x : E) : Set ℝ :=
  φ '' principalPositiveBelow a x

def functionalFragmentPos (φ : E →L[ℝ] ℝ) (a x : E) : ℝ :=
  sSup (functionalFragmentValues φ a x)

omit [IsOrderedAddMonoid E] in
theorem functionalFragmentValues_nonempty (φ : E →L[ℝ] ℝ) (a x : E) (hx : 0 ≤ x) :
    (functionalFragmentValues φ a x).Nonempty :=
  ⟨φ 0,0,⟨le_rfl,hx,0,by simp⟩,rfl⟩

theorem functionalFragmentPos_isLUB (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a x : E) (hx : 0 ≤ x) :
    IsLUB (functionalFragmentValues φ a x) (functionalFragmentPos φ a x) := by
  apply isLUB_csSup (functionalFragmentValues_nonempty φ a x hx)
  refine ⟨φ x,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  exact positive_operator_monotone hφ hy.2.1

theorem functionalFragmentPos_nonneg (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a x : E) (hx : 0 ≤ x) :
    0 ≤ functionalFragmentPos φ a x := by
  have h := (functionalFragmentPos_isLUB φ hφ a x hx).1
    (show φ 0 ∈ functionalFragmentValues φ a x from ⟨0,⟨le_rfl,hx,0,by simp⟩,rfl⟩)
  simpa only [map_zero] using h

theorem functionalFragmentPos_le (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a x : E) (hx : 0 ≤ x) :
    functionalFragmentPos φ a x ≤ φ x := by
  apply (functionalFragmentPos_isLUB φ hφ a x hx).2
  rintro _ ⟨y,hy,rfl⟩
  exact positive_operator_monotone hφ hy.2.1

omit [NormedSpace ℝ E] in
theorem principalPositiveBelow_add (a : E) {x y u v : E}
    (hu : u ∈ principalPositiveBelow a x) (hv : v ∈ principalPositiveBelow a y) :
    u+v ∈ principalPositiveBelow a (x+y) := by
  obtain ⟨hu0,hux,n,hn⟩ := hu
  obtain ⟨hv0,hvy,m,hm⟩ := hv
  refine ⟨add_nonneg hu0 hv0,add_le_add hux hvy,n+m,?_⟩
  simpa only [add_nsmul] using add_le_add hn hm

theorem functionalFragmentPos_add (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a x y : E)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    functionalFragmentPos φ a (x+y) = functionalFragmentPos φ a x + functionalFragmentPos φ a y := by
  have hmx := functionalFragmentPos_isLUB φ hφ a x hx
  have hmy := functionalFragmentPos_isLUB φ hφ a y hy
  have hmxy := functionalFragmentPos_isLUB φ hφ a (x+y) (add_nonneg hx hy)
  apply le_antisymm
  · apply hmxy.2
    rintro _ ⟨z,⟨hz0,hzxy,n,hzn⟩,rfl⟩
    obtain ⟨u,v,hu,hux,hv,hvy,huv⟩ := riesz_split_pair hz0 hx hy hzxy
    have huz : u ≤ z := by rw [← huv]; exact le_add_of_nonneg_right hv
    have hvz : v ≤ z := by rw [← huv]; exact le_add_of_nonneg_left hu
    have hum : φ u ≤ functionalFragmentPos φ a x := hmx.1 ⟨u,⟨hu,hux,n,huz.trans hzn⟩,rfl⟩
    have hvm : φ v ≤ functionalFragmentPos φ a y := hmy.1 ⟨v,⟨hv,hvy,n,hvz.trans hzn⟩,rfl⟩
    rw [← huv,map_add]
    exact add_le_add hum hvm
  · have hinner (v : E) (hv : v ∈ principalPositiveBelow a y) :
        functionalFragmentPos φ a x + φ v ≤ functionalFragmentPos φ a (x+y) := by
      apply le_sub_iff_add_le.mp
      apply hmx.2
      rintro _ ⟨u,hu,rfl⟩
      apply le_sub_iff_add_le.mpr
      have h := hmxy.1 ⟨u+v,principalPositiveBelow_add a hu hv,rfl⟩
      simpa only [map_add] using h
    apply le_sub_iff_add_le'.mp
    apply hmy.2
    rintro _ ⟨v,hv,rfl⟩
    exact le_sub_iff_add_le'.mpr (hinner v hv)

theorem functionalFragmentPos_norm_le (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a x : E) (hx : 0 ≤ x) :
    ‖functionalFragmentPos φ a x‖ ≤ ‖φ‖ * ‖x‖ := by
  rw [Real.norm_eq_abs,abs_of_nonneg (functionalFragmentPos_nonneg φ hφ a x hx)]
  exact (functionalFragmentPos_le φ hφ a x hx).trans ((le_abs_self _).trans (φ.le_opNorm x))

theorem functionalFragmentPos_self (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a : E) (ha : 0 ≤ a) :
    functionalFragmentPos φ a a = φ a := by
  apply le_antisymm (functionalFragmentPos_le φ hφ a a ha)
  exact (functionalFragmentPos_isLUB φ hφ a a ha).1 ⟨a,⟨ha,le_rfl,1,by simp⟩,rfl⟩

omit [NormedSpace ℝ E] in
theorem eq_zero_of_le_nsmul_of_inf_eq_zero {a x z : E} (ha : 0 ≤ a)
    (hax : a ⊓ x = 0) (n : ℕ) (hz : 0 ≤ z) (hza : z ≤ n • a) (hzx : z ≤ x) : z = 0 := by
  induction n generalizing z with
  | zero => exact le_antisymm (by simpa only [zero_nsmul] using hza) hz
  | succ n ih =>
    obtain ⟨u,v,hu,hun,hv,hva,huv⟩ := riesz_split_pair hz (nsmul_nonneg ha n) ha
      (by simpa only [succ_nsmul] using hza)
    have huz : u ≤ z := by rw [← huv]; exact le_add_of_nonneg_right hv
    have hvz : v ≤ z := by rw [← huv]; exact le_add_of_nonneg_left hu
    have hu0 := ih hu hun (huz.trans hzx)
    have hv0 : v = 0 := le_antisymm ((le_inf hva (hvz.trans hzx)).trans_eq hax) hv
    rw [← huv,hu0,hv0,add_zero]

theorem functionalFragmentPos_disjoint (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ)
    {a x : E} (ha : 0 ≤ a) (hx : 0 ≤ x) (hax : a ⊓ x = 0) :
    functionalFragmentPos φ a x = 0 := by
  apply le_antisymm _ (functionalFragmentPos_nonneg φ hφ a x hx)
  apply (functionalFragmentPos_isLUB φ hφ a x hx).2
  rintro _ ⟨z,⟨hz,hzx,n,hzn⟩,rfl⟩
  rw [eq_zero_of_le_nsmul_of_inf_eq_zero ha hax n hz hzn hzx,map_zero]

end ThesisCommon
