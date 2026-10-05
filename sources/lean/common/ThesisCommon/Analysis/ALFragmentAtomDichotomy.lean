import ThesisCommon.Analysis.ALFragmentDensityAtoms
import ThesisCommon.Analysis.ALAtomicRepresentationAtoms

/-! A dominated positive lattice atom has an actual atomic fragment carrier.
Its maximal scalar multiple below the given positive vector is a fragment.
Consequently every density-homogeneous fragment is either a positive lattice
atom or has no positive lattice atoms below it. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

omit [HasSolidNorm E] in
theorem IsPositiveLatticeAtom.fragment_eq_zero_or_self {a y : E}
    (ha : IsPositiveLatticeAtom a) (hy : IsPositiveFragment y a) : y = 0 ∨ y = a := by
  obtain ⟨r, hr, hyr⟩ := ha.2.2 y hy.1 hy.2.1
  obtain ⟨s, hs, hys⟩ := ha.2.2 (a-y) (sub_nonneg.mpr hy.2.1) (sub_le_self a hy.1)
  rcases le_total r s with hrs | hsr
  · left
    have hle : y ≤ a-y := by
      rw [hys, hyr]
      exact smul_le_smul_of_nonneg_right hrs ha.1
    simpa only [inf_eq_left.mpr hle] using hy.2.2
  · right
    have hle : a-y ≤ y := by
      rw [hys, hyr]
      exact smul_le_smul_of_nonneg_right hsr ha.1
    have hz : a-y = 0 := by simpa only [inf_eq_right.mpr hle] using hy.2.2
    exact (sub_eq_zero.mp hz).symm

/-- The largest scalar multiple of a dominated positive atom is an actual
nonzero atomic fragment, rather than merely a principal-ideal element. -/
theorem exists_positiveLatticeAtom_fragment_of_le [OrderClosedTopology E]
    {a x : E} (ha : IsPositiveLatticeAtom a) (hax : a ≤ x) :
    ∃ y : E, IsPositiveFragment y x ∧ IsPositiveLatticeAtom y ∧ a ≤ y := by
  let s : Set ℝ := {r | 0 ≤ r ∧ r • a ≤ x}
  have hx : 0 ≤ x := ha.1.trans hax
  have h1 : (1 : ℝ) ∈ s := ⟨zero_le_one, by simpa using hax⟩
  have hane : 0 < ‖a‖ := norm_pos_iff.mpr ha.2.1
  have hbound : BddAbove s := by
    refine ⟨‖x‖ / ‖a‖, ?_⟩
    intro r hr
    apply (le_div_iff₀ hane).mpr
    calc
      r * ‖a‖ = ‖r • a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
      _ ≤ ‖x‖ := norm_le_norm_of_abs_le_abs (by
        rw [abs_of_nonneg (smul_nonneg hr.1 ha.1), abs_of_nonneg hx]
        exact hr.2)
  have hclosed : IsClosed s :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le (continuous_id.smul continuous_const) continuous_const)
  let r := sSup s
  have hrmem : r ∈ s := hclosed.closure_subset_iff.mpr (Subset.refl s)
    (csSup_mem_closure ⟨1, h1⟩ hbound)
  have hr1 : 1 ≤ r := le_csSup hbound h1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  let y := r • a
  have hyAtom : IsPositiveLatticeAtom y := ha.smul_pos hrpos
  have hyx : y ≤ x := hrmem.2
  have hfrag : IsPositiveFragment y x := by
    refine ⟨hyAtom.1, hyx, ?_⟩
    let z := y ⊓ (x-y)
    have hz0 : 0 ≤ z := le_inf hyAtom.1 (sub_nonneg.mpr hyx)
    obtain ⟨t, ht, hzt⟩ := hyAtom.2.2 z hz0 inf_le_left
    have hcoeff : r + t*r ∈ s := by
      refine ⟨add_nonneg hrpos.le (mul_nonneg ht hrpos.le), ?_⟩
      calc
        (r + t*r) • a = y+z := by rw [hzt]; simp only [y, add_smul, smul_smul]
        _ ≤ x := add_le_of_le_sub_left (show z ≤ x-y from inf_le_right)
    have hle : r + t*r ≤ r := le_csSup hbound hcoeff
    have ht0 : t = 0 := by nlinarith
    change z = 0
    simpa only [ht0, zero_smul] using hzt
  refine ⟨y, hfrag, hyAtom, ?_⟩
  simpa only [one_smul] using smul_le_smul_of_nonneg_right hr1 ha.1

omit [HasSolidNorm E] in
theorem isAtom_positiveFragment_of_isPositiveLatticeAtom
    {e : E} [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e)
    (ha : IsPositiveLatticeAtom (positiveFragmentValue a)) : IsAtom a := by
  refine ⟨?_, fun b hba => ?_⟩
  · intro hz
    exact ha.2.1 (by simp [hz])
  have hbfrag : IsPositiveFragment (positiveFragmentValue b) (positiveFragmentValue a) := by
    refine ⟨positiveFragmentValue_nonneg b, hba.le, ?_⟩
    apply le_antisymm
    · exact (inf_le_inf_left _ (sub_le_sub_right (positiveFragmentValue_le a) _)).trans_eq
        (positiveFragmentValue_isFragment b).2.2
    · exact le_inf (positiveFragmentValue_nonneg b) (sub_nonneg.mpr hba.le)
  rcases ha.fragment_eq_zero_or_self hbfrag with hb | hb
  · exact positiveFragmentValue_injective e (by simpa using hb)
  · exact False.elim (hba.ne (positiveFragmentValue_injective e hb))

/-- A positive atom below a fragment produces a Boolean atom below that
fragment, with the original atom still below its value. -/
theorem exists_isAtom_positiveFragment_le_of_positiveLatticeAtom [OrderClosedTopology E]
    {e : E} [Fact (0 ≤ e)] (b : PositiveFragmentAlgebra e)
    {a : E} (ha : IsPositiveLatticeAtom a) (hab : a ≤ positiveFragmentValue b) :
    ∃ c : PositiveFragmentAlgebra e, c ≤ b ∧ IsAtom c ∧ a ≤ positiveFragmentValue c := by
  obtain ⟨y, hy, hyAtom, hay⟩ := exists_positiveLatticeAtom_fragment_of_le ha hab
  let c : PositiveFragmentAlgebra e := positiveFragmentOf
    (hy.trans (positiveFragmentValue_isFragment b))
  exact ⟨c, hy.2.1, isAtom_positiveFragment_of_isPositiveLatticeAtom c hyAtom, hay⟩

theorem isPositiveLatticeAtom_or_noPositiveAtomsBelow_of_densityHomogeneous
    [CompleteSpace E] [OrderClosedTopology E]
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    {e : E} [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) (ha : IsDensityHomogeneous a) :
    IsPositiveLatticeAtom (positiveFragmentValue a) ∨
      NoPositiveAtomsBelow (positiveFragmentValue a) := by
  classical
  by_cases hno : NoPositiveAtomsBelow (positiveFragmentValue a)
  · exact Or.inr hno
  left
  have hex : ∃ x : E, IsPositiveLatticeAtom x ∧ x ≤ positiveFragmentValue a := by
    by_contra hh
    apply hno
    intro x hx hxa hatom
    exact hh ⟨x, hatom, hxa⟩
  obtain ⟨x, hx, hxa⟩ := hex
  obtain ⟨b, hba, hb, _⟩ := exists_isAtom_positiveFragment_le_of_positiveLatticeAtom a hx hxa
  have hfin : (Iic b).Finite := by rw [hb.Iic_eq]; exact (finite_singleton b).insert ⊥
  letI : Finite (Iic b) := hfin.to_subtype
  have hden : principalDensity b < Cardinal.aleph0 := by
    rw [principalDensity, topologicalDensity_eq_card_of_finite]
    exact Cardinal.mk_lt_aleph0_iff.mpr inferInstance
  apply isPositiveLatticeAtom_of_homogeneous_finite_density hAL a ha
  rwa [ha.2 b hb.1 hba] at hden

end ThesisCommon
