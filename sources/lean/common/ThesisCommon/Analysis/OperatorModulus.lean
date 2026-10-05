import ThesisCommon.Analysis.OperatorModulusPositive
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Topology.Instances.RealVectorSpace

/-! The actual bounded modulus operator between real AL-spaces.
The positive-cone supremum is extended additively using positive/negative parts.
Its proved norm bound gives continuity and hence real linearity. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice F]
variable [IsOrderedAddMonoid F] [HasSolidNorm F] [CompleteSpace F] [OrderClosedTopology F]

def operatorModulusFn
    (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (T : E →L[ℝ] F) (x : E) : F :=
  operatorModulusPos hALE hALF T x⁺ (posPart_nonneg x) -
    operatorModulusPos hALE hALF T x⁻ (negPart_nonneg x)

variable (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
variable (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
variable (T : E →L[ℝ] F)

/-- The extension is independent of the chosen positive difference. -/
theorem operatorModulusFn_sub (a b : E) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    operatorModulusFn hALE hALF T (a - b) =
      operatorModulusPos hALE hALF T a ha - operatorModulusPos hALE hALF T b hb := by
  have heq : (a - b)⁺ + b = a + (a - b)⁻ :=
    sub_eq_sub_iff_add_eq_add.mp (posPart_sub_negPart (a - b))
  apply sub_eq_sub_iff_add_eq_add.mpr
  rw [← operatorModulusPos_add hALE hALF T _ _ (posPart_nonneg _) hb,
    ← operatorModulusPos_add hALE hALF T _ _ ha (negPart_nonneg _)]
  have heq' : (⟨(a - b)⁺ + b, add_nonneg (posPart_nonneg _) hb⟩ : {z : E // 0 ≤ z}) =
      ⟨a + (a - b)⁻, add_nonneg ha (negPart_nonneg _)⟩ := Subtype.ext heq
  exact congrArg (fun q : {z : E // 0 ≤ z} => operatorModulusPos hALE hALF T q.1 q.2) heq'

theorem operatorModulusFn_add (x y : E) :
    operatorModulusFn hALE hALF T (x + y) =
      operatorModulusFn hALE hALF T x + operatorModulusFn hALE hALF T y := by
  have heq : x + y = (x⁺ + y⁺) - (x⁻ + y⁻) := by
    calc
      x + y = (x⁺ - x⁻) + (y⁺ - y⁻) := by rw [posPart_sub_negPart, posPart_sub_negPart]
      _ = (x⁺ + y⁺) - (x⁻ + y⁻) := by abel
  rw [heq, operatorModulusFn_sub hALE hALF T _ _
      (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (add_nonneg (negPart_nonneg x) (negPart_nonneg y)),
    operatorModulusPos_add hALE hALF T _ _ (posPart_nonneg x) (posPart_nonneg y),
    operatorModulusPos_add hALE hALF T _ _ (negPart_nonneg x) (negPart_nonneg y)]
  dsimp [operatorModulusFn]
  abel

theorem norm_operatorModulusFn_le (x : E) :
    ‖operatorModulusFn hALE hALF T x‖ ≤ ‖T‖ * ‖x‖ := by
  have hnorm : ‖x⁺‖ + ‖x⁻‖ = ‖x‖ := by
    rw [← hALE _ _ (posPart_nonneg x) (negPart_nonneg x), posPart_add_negPart, norm_abs_eq_norm]
  calc
    ‖operatorModulusFn hALE hALF T x‖ ≤
        ‖operatorModulusPos hALE hALF T x⁺ (posPart_nonneg x)‖ +
          ‖operatorModulusPos hALE hALF T x⁻ (negPart_nonneg x)‖ := norm_sub_le _ _
    _ ≤ ‖T‖ * ‖x⁺‖ + ‖T‖ * ‖x⁻‖ :=
      add_le_add (norm_operatorModulusPos_le hALE hALF T _ _) (norm_operatorModulusPos_le hALE hALF T _ _)
    _ = ‖T‖ * ‖x‖ := by rw [← mul_add, hnorm]

def operatorModulusAddHom
    (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (T : E →L[ℝ] F) : E →+ F where
  toFun := operatorModulusFn hALE hALF T
  map_zero' := by simp [operatorModulusFn]
  map_add' := operatorModulusFn_add hALE hALF T

/-- The constructed bounded real-linear modulus. No regularity or modulus
existence hypothesis is used: both follow from the AL norm structure. -/
def operatorModulus
    (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (T : E →L[ℝ] F) : E →L[ℝ] F :=
  (operatorModulusAddHom hALE hALF T).toRealLinearMap
    (AddMonoidHomClass.continuous_of_bound (operatorModulusAddHom hALE hALF T) ‖T‖
      (norm_operatorModulusFn_le hALE hALF T))

theorem operatorModulus_apply (x : E) :
    operatorModulus hALE hALF T x = operatorModulusFn hALE hALF T x := rfl

theorem operatorModulus_apply_of_nonneg (x : E) (hx : 0 ≤ x) :
    operatorModulus hALE hALF T x = operatorModulusPos hALE hALF T x hx := by
  have h := operatorModulusFn_sub hALE hALF T x 0 hx (le_refl 0)
  simpa [operatorModulusPos_zero] using h

theorem operatorModulus_nonneg (x : E) (hx : 0 ≤ x) :
    0 ≤ operatorModulus hALE hALF T x := by
  rw [operatorModulus_apply_of_nonneg hALE hALF T x hx]
  exact operatorModulusPos_nonneg hALE hALF T x hx

theorem operatorModulus_dominates (x : E) (hx : 0 ≤ x) :
    |T x| ≤ operatorModulus hALE hALF T x := by
  rw [operatorModulus_apply_of_nonneg hALE hALF T x hx]
  exact abs_apply_le_operatorModulusPos hALE hALF T x hx

/-- Leastness among all bounded linear operators dominating both T and -T
on the positive cone; this is the operator-lattice modulus property. -/
theorem operatorModulus_least (R : E →L[ℝ] F)
    (hR : ∀ x : E, 0 ≤ x → |T x| ≤ R x) (x : E) (hx : 0 ≤ x) :
    operatorModulus hALE hALF T x ≤ R x := by
  rw [operatorModulus_apply_of_nonneg hALE hALF T x hx]
  apply (operatorModulusPos_isLUB hALE hALF T x hx).2
  rintro _ ⟨d, rfl⟩
  calc
    d.value T ≤ ∑ i, R (d.part i) := Finset.sum_le_sum fun i _ => hR _ (d.nonneg i)
    _ = R x := by rw [← map_sum, d.sum_eq]

theorem abs_apply_le_operatorModulus_abs (x : E) :
    |T x| ≤ operatorModulus hALE hALF T |x| := by
  calc
    |T x| = |T x⁺ - T x⁻| := by rw [← map_sub, posPart_sub_negPart]
    _ ≤ |T x⁺| + |T x⁻| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (T x⁺) (-(T x⁻))
    _ ≤ operatorModulus hALE hALF T x⁺ + operatorModulus hALE hALF T x⁻ :=
      add_le_add (operatorModulus_dominates hALE hALF T _ (posPart_nonneg x))
        (operatorModulus_dominates hALE hALF T _ (negPart_nonneg x))
    _ = operatorModulus hALE hALF T |x| := by rw [← map_add, posPart_add_negPart]

/-- The modulus has precisely the original operator norm. -/
theorem norm_operatorModulus : ‖operatorModulus hALE hALF T‖ = ‖T‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (norm_operatorModulusFn_le hALE hALF T)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    calc
      ‖T x‖ ≤ ‖operatorModulus hALE hALF T |x|‖ := by
        apply norm_le_norm_of_abs_le_abs
        rw [abs_of_nonneg (operatorModulus_nonneg hALE hALF T _ (abs_nonneg x))]
        exact abs_apply_le_operatorModulus_abs hALE hALF T x
      _ ≤ ‖operatorModulus hALE hALF T‖ * ‖|x|‖ := (operatorModulus hALE hALF T).le_opNorm _
      _ = ‖operatorModulus hALE hALF T‖ * ‖x‖ := by rw [norm_abs_eq_norm]

include hALE hALF in
/-- Every bounded operator between real AL-spaces is regular: the positive
and negative parts are (|T|+T)/2 and (|T|-T)/2. -/
theorem exists_positive_operator_decomposition [IsOrderedModule ℝ F] :
    ∃ P Q : E →L[ℝ] F, (∀ x, 0 ≤ x → 0 ≤ P x) ∧
      (∀ x, 0 ≤ x → 0 ≤ Q x) ∧ T = P - Q := by
  let M := operatorModulus hALE hALF T
  refine ⟨(1 / 2 : ℝ) • (M + T), (1 / 2 : ℝ) • (M - T), ?_, ?_, ?_⟩
  · intro x hx
    change 0 ≤ (1 / 2 : ℝ) • (M x + T x)
    apply smul_nonneg (by norm_num)
    have h := add_le_add_right ((neg_le_abs (T x)).trans (operatorModulus_dominates hALE hALF T x hx)) (T x)
    simpa only [neg_add_cancel] using h
  · intro x hx
    change 0 ≤ (1 / 2 : ℝ) • (M x - T x)
    apply smul_nonneg (by norm_num)
    exact sub_nonneg.mpr ((le_abs_self (T x)).trans (operatorModulus_dominates hALE hALF T x hx))
  · rw [← smul_sub]
    have h : (M + T) - (M - T) = (2 : ℝ) • T := by rw [two_smul]; abel
    rw [h, smul_smul]
    norm_num

end ThesisCommon
