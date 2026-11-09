import Mathlib.Algebra.Field.Opposite
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-! The existing opposite-ring metric and norm form a normed division ring.
The norm of its reversed product is multiplicative because the real-valued
norm factors commute. No norm or topology is replaced. -/

namespace BanachIsometric.MetricGeometry

instance normedDivisionRingOpposite {R : Type*} [NormedDivisionRing R] :
    NormedDivisionRing Rᵐᵒᵖ where
  __ := inferInstanceAs (DivisionRing Rᵐᵒᵖ)
  __ := inferInstanceAs (Norm Rᵐᵒᵖ)
  __ := inferInstanceAs (MetricSpace Rᵐᵒᵖ)
  dist_eq x y := dist_eq_norm x y
  norm_mul x y := by
    change ‖y.unop * x.unop‖ = ‖x.unop‖ * ‖y.unop‖
    rw [norm_mul, mul_comm]

end BanachIsometric.MetricGeometry

