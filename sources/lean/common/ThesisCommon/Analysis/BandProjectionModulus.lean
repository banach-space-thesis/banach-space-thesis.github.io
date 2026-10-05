import ThesisCommon.Analysis.BandProjection
import ThesisCommon.Analysis.LatticeDisjointness

/-! Modulus and lattice identities for the constructed band projection. -/
noncomputable section

namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
variable {I : Submodule ℝ E}

namespace IsOrderClosedIdeal
variable (hI : IsOrderClosedIdeal I)

/-- The band and complementary components split the modulus additively. -/
theorem abs_band_decomposition (x : E) :
    |x| = |bandProjection hI x| + |x - bandProjection hI x| := by
  have hdisj : |bandProjection hI x| ⊓ |x - bandProjection hI x| = 0 := by
    rw [inf_comm]
    exact hI.residual_disjoint x (hI.bandProjection_mem x)
  calc
    |x| = |bandProjection hI x + (x - bandProjection hI x)| := by
      congr 1
      abel
    _ = |bandProjection hI x| + |x - bandProjection hI x| :=
      lattice_abs_add_of_disjoint hdisj

/-- The absolute value of the complementary component is still complementary. -/
theorem bandProjection_abs_residual_eq_zero (x : E) :
    bandProjection hI |x - bandProjection hI x| = 0 := by
  apply (hI.bandProjection_eq_zero_iff _).mpr
  intro y hy
  simpa only [abs_abs] using hI.residual_disjoint x hy

/-- The actual constructed band projection preserves lattice modulus. -/
theorem bandProjection_abs (x : E) :
    bandProjection hI |x| = |bandProjection hI x| := by
  calc
    bandProjection hI |x| =
        bandProjection hI (|bandProjection hI x| + |x - bandProjection hI x|) :=
      congrArg (bandProjection hI) (hI.abs_band_decomposition x)
    _ = |bandProjection hI x| := by
      rw [map_add, hI.bandProjection_eq_self (hI.abs_mem (hI.bandProjection_mem x)),
        hI.bandProjection_abs_residual_eq_zero, add_zero]

/-- The complementary projection also preserves modulus. -/
theorem abs_residual (x : E) :
    |x - bandProjection hI x| = |x| - bandProjection hI |x| := by
  rw [hI.bandProjection_abs, hI.abs_band_decomposition x]
  abel

/-- The constructed projection preserves binary suprema. -/
theorem bandProjection_sup (x y : E) :
    bandProjection hI (x ⊔ y) = bandProjection hI x ⊔ bandProjection hI y := by
  apply lattice_two_nsmul_injective
  calc
    2 • bandProjection hI (x ⊔ y) = bandProjection hI (2 • (x ⊔ y)) :=
      (map_nsmul (bandProjection hI) 2 (x ⊔ y)).symm
    _ = bandProjection hI x + bandProjection hI y +
        |bandProjection hI y - bandProjection hI x| := by
      rw [two_nsmul_sup_eq_add_add_abs_sub, map_add, map_add,
        hI.bandProjection_abs, map_sub]
    _ = 2 • (bandProjection hI x ⊔ bandProjection hI y) :=
      (two_nsmul_sup_eq_add_add_abs_sub _ _).symm

/-- The constructed projection preserves binary infima. -/
theorem bandProjection_inf (x y : E) :
    bandProjection hI (x ⊓ y) = bandProjection hI x ⊓ bandProjection hI y := by
  apply lattice_two_nsmul_injective
  calc
    2 • bandProjection hI (x ⊓ y) = bandProjection hI (2 • (x ⊓ y)) :=
      (map_nsmul (bandProjection hI) 2 (x ⊓ y)).symm
    _ = bandProjection hI x + bandProjection hI y -
        |bandProjection hI y - bandProjection hI x| := by
      rw [two_nsmul_inf_eq_add_sub_abs_sub, map_sub, map_add,
        hI.bandProjection_abs, map_sub]
    _ = 2 • (bandProjection hI x ⊓ bandProjection hI y) :=
      (two_nsmul_inf_eq_add_sub_abs_sub _ _).symm

end IsOrderClosedIdeal
end ThesisCommon
