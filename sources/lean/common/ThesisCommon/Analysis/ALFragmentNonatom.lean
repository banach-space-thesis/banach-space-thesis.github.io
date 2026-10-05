import ThesisCommon.Analysis.ALFragmentPrincipal

/-! A positive nonatom in a complete AL-lattice has a nontrivial fragment. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
  [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ u v : E, 0 ≤ u → 0 ≤ v → ‖u+v‖ = ‖u‖+‖v‖)
include hAL

theorem al_eq_of_le_of_norm_eq {x y : E} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hnorm : ‖x‖ = ‖y‖) : x = y := by
  have h := al_norm_sub_of_le hAL hx hxy
  rw [← hnorm, sub_self] at h
  exact (sub_eq_zero.mp (norm_eq_zero.mp h)).symm

theorem al_nonatom_disjoint_pair {x : E} (hx : 0 ≤ x) (hxne : x ≠ 0)
    (hnot : ¬ IsPositiveLatticeAtom x) :
    ∃ a b : E, 0 ≤ a ∧ a ≤ x ∧ a ≠ 0 ∧ 0 ≤ b ∧ b ≤ x ∧ b ≠ 0 ∧ a ⊓ b = 0 := by
  classical
  have hbad : ¬ ∀ y : E, 0 ≤ y → y ≤ x → ∃ r : ℝ, 0 ≤ r ∧ y = r • x :=
    fun h => hnot ⟨hx,hxne,h⟩
  push_neg at hbad
  obtain ⟨y,hy,hyx,hynot⟩ := hbad
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hyn : ‖y‖ ≤ ‖x‖ := norm_le_norm_of_abs_le_abs (by
    rw [abs_of_nonneg hy, abs_of_nonneg hx]
    exact hyx)
  let r : ℝ := ‖y‖ / ‖x‖
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) hxn.le
  have hr1 : r ≤ 1 := (div_le_one hxn).mpr hyn
  have hrx0 : 0 ≤ r • x := smul_nonneg hr0 hx
  have hrxx : r • x ≤ x := by simpa using smul_le_smul_of_nonneg_right hr1 hx
  have hrnorm : ‖r • x‖ = ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact div_mul_cancel₀ _ hxn.ne'
  have hne : y ≠ r • x := hynot r hr0
  have hnle : ¬ y ≤ r • x := fun h => hne (al_eq_of_le_of_norm_eq hAL hy h hrnorm.symm)
  have hnge : ¬ r • x ≤ y := fun h => hne (al_eq_of_le_of_norm_eq hAL hrx0 h hrnorm).symm
  let d := y-r • x
  have hapos : 0 ≤ d⁺ := posPart_nonneg d
  have hbpos : 0 ≤ d⁻ := negPart_nonneg d
  have ha_le : d⁺ ≤ x := sup_le ((sub_le_self y hrx0).trans hyx) hx
  have hb_le : d⁻ ≤ x := by
    change (-(y-r • x)) ⊔ 0 ≤ x
    rw [neg_sub]
    exact sup_le ((sub_le_self (r • x) hy).trans hrxx) hx
  have hane : d⁺ ≠ 0 := by
    intro h
    have hd : d ≤ 0 := (le_posPart d).trans_eq h
    exact hnle (sub_nonpos.mp hd)
  have hbne : d⁻ ≠ 0 := by
    intro h
    have hd : -d ≤ 0 := (show -d ≤ d⁻ from le_sup_left).trans_eq h
    have hnonneg : 0 ≤ d := neg_nonpos.mp hd
    exact hnge (sub_nonneg.mp hnonneg)
  exact ⟨d⁺,d⁻,hapos,ha_le,hane,hbpos,hb_le,hbne,posPart_inf_negPart_eq_zero d⟩

theorem al_exists_nontrivial_fragment {x : E} (hx : 0 ≤ x) (hxne : x ≠ 0)
    (hnot : ¬ IsPositiveLatticeAtom x) :
    ∃ y : E, IsPositiveFragment y x ∧ y ≠ 0 ∧ y ≠ x := by
  obtain ⟨a,b,ha,hax,hane,hb,hbx,hbne,hab⟩ := al_nonatom_disjoint_pair hAL hx hxne hnot
  obtain ⟨y,hy,hay,hdisj⟩ := al_exists_principal_fragment hAL ha hx
  rw [inf_eq_left.mpr hax] at hay
  refine ⟨y,hy,?_,?_⟩
  · intro hy0
    exact hane (le_antisymm (hay.trans_eq hy0) ha)
  · intro hyx
    have heq := hdisj b hb hab
    rw [hyx,inf_eq_right.mpr hbx] at heq
    exact hbne heq

theorem al_exists_small_half_fragment {x : E} (hx : 0 ≤ x) (hxne : x ≠ 0)
    (hnot : ¬ IsPositiveLatticeAtom x) :
    ∃ y : E, IsPositiveFragment y x ∧ y ≠ 0 ∧ ‖y‖ ≤ ‖x‖ / 2 := by
  obtain ⟨y,hy,hyne,hyx⟩ := al_exists_nontrivial_fragment hAL hx hxne hnot
  have hsum : ‖y‖ + ‖x-y‖ = ‖x‖ := by
    rw [← hAL y (x-y) hy.1 (sub_nonneg.mpr hy.2.1)]
    congr 1
    abel
  by_cases hsmall : ‖y‖ ≤ ‖x‖/2
  · exact ⟨y,hy,hyne,hsmall⟩
  · refine ⟨x-y,hy.compl,?_,by linarith⟩
    intro hzero
    exact hyx (sub_eq_zero.mp hzero).symm

theorem al_exists_arbitrarily_small_fragment {x : E} (hx : 0 ≤ x) (hxne : x ≠ 0)
    (hno : NoPositiveAtomsBelow x) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : E, IsPositiveFragment y x ∧ y ≠ 0 ∧ ‖y‖ < ε := by
  have hsequence (n : ℕ) : ∃ y : E,
      IsPositiveFragment y x ∧ y ≠ 0 ∧ ‖y‖ ≤ (1/2 : ℝ)^n * ‖x‖ := by
    induction n with
    | zero => exact ⟨x,IsPositiveFragment.self hx,hxne,by simp⟩
    | succ n ih =>
        obtain ⟨y,hy,hyne,hynorm⟩ := ih
        obtain ⟨z,hz,hzne,hznorm⟩ := al_exists_small_half_fragment hAL hy.1 hyne
          (hno y hy.1 hy.2.1)
        refine ⟨z,hz.trans hy,hzne,?_⟩
        rw [pow_succ]
        nlinarith
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hxn) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨y,hy,hyne,hynorm⟩ := hsequence n
  exact ⟨y,hy,hyne,hynorm.trans_lt ((lt_div_iff₀ hxn).mp hn)⟩

end ThesisCommon
