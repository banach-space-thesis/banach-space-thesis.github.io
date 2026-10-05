import ThesisCommon.Analysis.BanachLattice
import Mathlib.Algebra.Order.Monoid.Prod

/-! The genuine coordinatewise real Banach lattice structure on a product,
with the ordinary maximum norm. -/
namespace ThesisCommon
namespace SigmaComplexLatticeProduct
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice F]
  [IsOrderedAddMonoid F] [IsOrderedModule ℝ F] [HasSolidNorm F]

scoped instance orderedModule : IsOrderedModule ℝ (E × F) where
  smul_le_smul_of_nonneg_left _r hr _x _y hxy :=
    ⟨smul_le_smul_of_nonneg_left hxy.1 hr,smul_le_smul_of_nonneg_left hxy.2 hr⟩
  smul_le_smul_of_nonneg_right _x hx _r _s hrs :=
    ⟨smul_le_smul_of_nonneg_right hrs hx.1,smul_le_smul_of_nonneg_right hrs hx.2⟩

scoped instance solidNorm : HasSolidNorm (E × F) where
  solid {_x _y} h := max_le_max (norm_le_norm_of_abs_le_abs h.1) (norm_le_norm_of_abs_le_abs h.2)

end SigmaComplexLatticeProduct

theorem complexLatticeProduct_abs {E F : Type*} [NormedAddCommGroup E] [Lattice E]
    [NormedAddCommGroup F] [Lattice F] (x : E) (y : F) :
    |(x,y)| = (|x|,|y|) := rfl

end ThesisCommon

