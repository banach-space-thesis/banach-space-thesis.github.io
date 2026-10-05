import ThesisCommon.ALSpace

/-! A concrete real lattice supplies the scalar-uniform intrinsic model.
The real form is the entire space and the rotation supremum is x ⊔ (-x),
because the real scalars of norm one are precisely 1 and -1. -/
noncomputable section
namespace ThesisCommon
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

instance realTop_lattice : Lattice (⊤ : Submodule ℝ E) :=
  Subtype.lattice (by intros; exact Submodule.mem_top) (by intros; exact Submodule.mem_top)

instance realTop_orderedAdd : IsOrderedAddMonoid (⊤ : Submodule ℝ E) where
  add_le_add_left a b h c := by
    change (c : E) + (a : E) ≤ (c : E) + (b : E)
    exact add_le_add_left (show (a : E) ≤ (b : E) from h) _

instance realTop_orderedModule : IsOrderedModule ℝ (⊤ : Submodule ℝ E) :=
  IsOrderedModule.of_smul_nonneg fun r hr x hx => by
    change (0 : E) ≤ r • (x : E)
    exact smul_nonneg hr (show (0 : E) ≤ (x : E) from hx)

instance realTop_solidNorm : HasSolidNorm (⊤ : Submodule ℝ E) where
  solid {x y} h := by
    change ‖(x : E)‖ ≤ ‖(y : E)‖
    exact norm_le_norm_of_abs_le_abs (show |(x : E)| ≤ |(y : E)| from h)

/-- Real lattices, without any representation theorem assumed. -/
def realBanachLatticeModel : BanachLatticeModel ℝ E where
  realForm := ⊤
  closed_realForm := isClosed_univ
  realPart := (ContinuousLinearMap.id ℝ E).codRestrict ⊤ (fun _ => Submodule.mem_top)
  realPart_coe _ := rfl
  realPart_I := by intro x; apply Subtype.ext; simp
  decomposition := by intro z; simp
  lattice := realTop_lattice E
  orderedAdd := realTop_orderedAdd E
  orderedModule := realTop_orderedModule E
  solidNorm := realTop_solidNorm E
  modulus z := ⟨|z|, Submodule.mem_top⟩
  modulus_lub := by
    intro z
    constructor
    · rintro _ ⟨a, ha, rfl⟩
      have ha' : |a| = 1 := by simpa only [Real.norm_eq_abs] using ha
      rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp ha' with rfl | rfl
      · change (1 : ℝ) • z ≤ |z|
        simpa using le_abs_self z
      · change (-1 : ℝ) • z ≤ |z|
        simpa using neg_le_abs z
    · intro b hb
      change z ⊔ (-z) ≤ (b : E)
      apply sup_le
      · have h := hb ⟨1, by norm_num, rfl⟩
        change (1 : ℝ) • z ≤ (b : E) at h
        simpa using h
      · have h := hb ⟨-1, by norm_num, rfl⟩
        change (-1 : ℝ) • z ≤ (b : E) at h
        simpa using h
  norm_modulus z := norm_abs_eq_norm z

/-- The usual positive-cone AL identity implies the intrinsic AL predicate. -/
theorem isALSpace_of_real_lattice
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) : IsALSpace ℝ E := by
  refine ⟨realBanachLatticeModel E, ?_⟩
  intro x y hx hy
  exact hAL (x : E) (y : E) hx hy

theorem RealBanachLattice.IsAL.isALSpace {B : RealBanachLattice} (h : B.IsAL) :
    IsALSpace ℝ B := isALSpace_of_real_lattice B h

end ThesisCommon
