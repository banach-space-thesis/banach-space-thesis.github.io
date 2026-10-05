import ThesisCommon.Analysis.ComplexL1ModulusSup
import Mathlib.Topology.Instances.RealVectorSpace

/-! Extend the constructed positive-cone modulus to an actual bounded real
linear operator. The target norm bound is proved, not assumed. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def complexOperatorModulusFn (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) (x : Lp ℝ 1 μ) : Lp ℝ 1 ν :=
  complexOperatorModulusPos T x⁺ (posPart_nonneg x) -
    complexOperatorModulusPos T x⁻ (negPart_nonneg x)

theorem complexOperatorModulusFn_sub (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (a b : Lp ℝ 1 μ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    complexOperatorModulusFn T (a-b) =
      complexOperatorModulusPos T a ha - complexOperatorModulusPos T b hb := by
  have heq : (a-b)⁺ + b = a + (a-b)⁻ :=
    sub_eq_sub_iff_add_eq_add.mp (posPart_sub_negPart (a-b))
  apply sub_eq_sub_iff_add_eq_add.mpr
  rw [← complexOperatorModulusPos_add T _ _ (posPart_nonneg _) hb,
    ← complexOperatorModulusPos_add T _ _ ha (negPart_nonneg _)]
  have heq' : (⟨(a-b)⁺+b, add_nonneg (posPart_nonneg _) hb⟩ : {z : Lp ℝ 1 μ // 0 ≤ z}) =
      ⟨a+(a-b)⁻,add_nonneg ha (negPart_nonneg _)⟩ := Subtype.ext heq
  exact congrArg (fun q : {z : Lp ℝ 1 μ // 0 ≤ z} => complexOperatorModulusPos T q.1 q.2) heq'

theorem complexOperatorModulusFn_add (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) (x y : Lp ℝ 1 μ) :
    complexOperatorModulusFn T (x+y) = complexOperatorModulusFn T x + complexOperatorModulusFn T y := by
  have heq : x+y = (x⁺+y⁺)-(x⁻+y⁻) := by
    calc
      x+y = (x⁺-x⁻)+(y⁺-y⁻) := by rw [posPart_sub_negPart, posPart_sub_negPart]
      _ = _ := by abel
  rw [heq, complexOperatorModulusFn_sub T _ _
      (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (add_nonneg (negPart_nonneg x) (negPart_nonneg y)),
    complexOperatorModulusPos_add T _ _ (posPart_nonneg x) (posPart_nonneg y),
    complexOperatorModulusPos_add T _ _ (negPart_nonneg x) (negPart_nonneg y)]
  dsimp [complexOperatorModulusFn]
  abel

theorem norm_complexOperatorModulusFn_le (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) (x : Lp ℝ 1 μ) :
    ‖complexOperatorModulusFn T x‖ ≤ ‖T‖*‖x‖ := by
  have hn : ‖x⁺‖+‖x⁻‖ = ‖x‖ := by
    rw [← lOne_norm_add_of_nonneg μ _ _ (posPart_nonneg x) (negPart_nonneg x),
      posPart_add_negPart,norm_abs_eq_norm]
  calc
    ‖complexOperatorModulusFn T x‖ ≤ ‖complexOperatorModulusPos T x⁺ (posPart_nonneg x)‖ +
        ‖complexOperatorModulusPos T x⁻ (negPart_nonneg x)‖ := norm_sub_le _ _
    _ ≤ ‖T‖*‖x⁺‖+‖T‖*‖x⁻‖ :=
      add_le_add (norm_complexOperatorModulusPos_le T _ _) (norm_complexOperatorModulusPos_le T _ _)
    _ = ‖T‖*‖x‖ := by rw [← mul_add,hn]

def complexOperatorModulusAddHom (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) : Lp ℝ 1 μ →+ Lp ℝ 1 ν where
  toFun := complexOperatorModulusFn T
  map_zero' := by simp [complexOperatorModulusFn]
  map_add' := complexOperatorModulusFn_add T

def complexOperatorModulus (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  (complexOperatorModulusAddHom T).toRealLinearMap
    (AddMonoidHomClass.continuous_of_bound (complexOperatorModulusAddHom T) ‖T‖
      (norm_complexOperatorModulusFn_le T))

theorem complexOperatorModulus_apply_nonneg (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) : complexOperatorModulus T x = complexOperatorModulusPos T x hx := by
  have h := complexOperatorModulusFn_sub T x 0 hx (le_refl 0)
  simpa [complexOperatorModulusPos_zero] using h

theorem complexOperatorModulus_nonneg (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) : 0 ≤ complexOperatorModulus T x := by
  rw [complexOperatorModulus_apply_nonneg T x hx]
  exact complexOperatorModulusPos_nonneg T x hx

theorem complexOperatorModulus_dominates_nonneg (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) : complexL1Modulus (T x) ≤ complexOperatorModulus T x := by
  rw [complexOperatorModulus_apply_nonneg T x hx]
  exact complexOperatorModulusPos_dominates T x hx

theorem norm_complexOperatorModulus_le (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) :
    ‖complexOperatorModulus T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (norm_complexOperatorModulusFn_le T)

theorem complexOperatorModulus_least (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (R : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hR : ∀ x, 0 ≤ x → complexL1Modulus (T x) ≤ R x)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) : complexOperatorModulus T x ≤ R x := by
  rw [complexOperatorModulus_apply_nonneg T x hx]
  apply (complexOperatorModulusPos_isLUB T x hx).2
  rintro _ ⟨d,rfl⟩
  calc
    d.complexValue T ≤ ∑ i, R (d.part i) := Finset.sum_le_sum fun i _ => hR _ (d.nonneg i)
    _ = R x := by rw [← map_sum,d.sum_eq]

end ThesisCommon
