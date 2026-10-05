import ThesisCommon.Analysis.ALOrderCompleteness
import ThesisCommon.Analysis.FunctionalFragmentPositive

/-! Positive lattice atoms and fragments, with the algebra of nested fragments. -/
noncomputable section
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E]

def IsPositiveLatticeAtom (a : E) : Prop :=
  0 ≤ a ∧ a ≠ 0 ∧
    ∀ y : E, 0 ≤ y → y ≤ a → ∃ r : ℝ, 0 ≤ r ∧ y = r • a

def NoPositiveAtomsBelow (x : E) : Prop :=
  ∀ a : E, 0 ≤ a → a ≤ x → ¬ IsPositiveLatticeAtom a

theorem NoPositiveAtomsBelow.mono {x y : E} (hx : NoPositiveAtomsBelow x) (hyx : y ≤ x) :
    NoPositiveAtomsBelow y := fun a ha hay => hx a ha (hay.trans hyx)

def IsPositiveFragment (y x : E) : Prop :=
  0 ≤ y ∧ y ≤ x ∧ y ⊓ (x - y) = 0

theorem IsPositiveFragment.zero {x : E} (hx : 0 ≤ x) : IsPositiveFragment 0 x := by
  exact ⟨le_rfl, hx, by simp [inf_eq_left.mpr hx]⟩

theorem IsPositiveFragment.self {x : E} (hx : 0 ≤ x) : IsPositiveFragment x x := by
  exact ⟨hx, le_rfl, by simp [inf_eq_right.mpr hx]⟩

theorem IsPositiveFragment.compl {x y : E} (h : IsPositiveFragment y x) :
    IsPositiveFragment (x-y) x := by
  refine ⟨sub_nonneg.mpr h.2.1, sub_le_self x h.1, ?_⟩
  rw [sub_sub_cancel, inf_comm]
  exact h.2.2

theorem positive_inf_add_eq_zero {x y z : E} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxy : x ⊓ y = 0) (hxz : x ⊓ z = 0) : x ⊓ (y+z) = 0 := by
  let t := x ⊓ (y+z)
  obtain ⟨u,v,hu,huy,hv,hvz,huv⟩ :=
    riesz_split_pair (le_inf hx (add_nonneg hy hz)) hy hz
      (show t ≤ y+z from inf_le_right)
  have hut : u ≤ t := by
    change u ≤ x ⊓ (y+z)
    rw [← huv]
    exact le_add_of_nonneg_right hv
  have hvt : v ≤ t := by
    change v ≤ x ⊓ (y+z)
    rw [← huv]
    exact le_add_of_nonneg_left hu
  have hu0 : u = 0 := le_antisymm ((le_inf (hut.trans inf_le_left) huy).trans_eq hxy) hu
  have hv0 : v = 0 := le_antisymm ((le_inf (hvt.trans inf_le_left) hvz).trans_eq hxz) hv
  simpa [hu0,hv0] using huv.symm

theorem IsPositiveFragment.trans {x y z : E} (hy : IsPositiveFragment y z)
    (hz : IsPositiveFragment z x) : IsPositiveFragment y x := by
  refine ⟨hy.1, hy.2.1.trans hz.2.1, ?_⟩
  have hyz : y ⊓ (x-z) = 0 := le_antisymm
    ((inf_le_inf_right _ hy.2.1).trans_eq hz.2.2)
    (le_inf hy.1 (sub_nonneg.mpr hz.2.1))
  have h := positive_inf_add_eq_zero hy.1 (sub_nonneg.mpr hy.2.1)
    (sub_nonneg.mpr hz.2.1) hy.2.2 hyz
  have heq : z-y+(x-z) = x-y := by abel
  rwa [heq] at h

theorem IsPositiveFragment.add_compl {x y z : E} (hy : IsPositiveFragment y x)
    (hz : IsPositiveFragment z (x-y)) : IsPositiveFragment (y+z) x := by
  have hr : 0 ≤ x-(y+z) := sub_nonneg.mpr (by
    exact add_le_of_le_sub_left (by simpa only [add_comm] using hz.2.1))
  have hbound : x-(y+z) ≤ x-y := sub_le_sub_left (le_add_of_nonneg_right hz.1) _
  have hyr : y ⊓ (x-(y+z)) = 0 := le_antisymm
    ((inf_le_inf_left _ hbound).trans_eq hy.2.2) (le_inf hy.1 hr)
  have hzr : z ⊓ (x-(y+z)) = 0 := by
    have heq : x-(y+z) = (x-y)-z := by abel
    rw [heq]
    exact hz.2.2
  refine ⟨add_nonneg hy.1 hz.1, sub_nonneg.mp hr, ?_⟩
  rw [inf_comm]
  exact positive_inf_add_eq_zero hr hy.1 hz.1
    (by rw [inf_comm]; exact hyr) (by rw [inf_comm]; exact hzr)

theorem IsPositiveFragment.noAtoms_children {x y : E} (hy : IsPositiveFragment y x)
    (hx : NoPositiveAtomsBelow x) :
    NoPositiveAtomsBelow y ∧ NoPositiveAtomsBelow (x-y) :=
  ⟨hx.mono hy.2.1, hx.mono (sub_le_self _ hy.1)⟩

end ThesisCommon
