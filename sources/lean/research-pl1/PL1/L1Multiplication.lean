import PL1.ConvolutionL1

/-! # Actual multiplication by continuous real functions on Haar L1 -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PL1.L1Multiplication
open Walsh

variable (K : Type*) [RCLike K]

theorem integrable_product (q : C(Walsh.Group, ℝ)) (f : Lp K 1 haar) :
    Integrable (fun x => q x • f x) haar :=
  (L1.integrable_coeFn f).bdd_smul (𝕜 := ℝ) ‖q‖ q.continuous.aestronglyMeasurable
    (ae_of_all _ (fun x => q.norm_coe_le_norm x))

def product (q : C(Walsh.Group, ℝ)) (f : Lp K 1 haar) : Lp K 1 haar :=
  (integrable_product K q f).toL1 (fun x => q x • f x)

theorem coeFn_product (q : C(Walsh.Group, ℝ)) (f : Lp K 1 haar) :
    product K q f =ᵐ[haar] fun x => q x • f x :=
  (integrable_product K q f).coeFn_toL1

theorem product_add (q : C(Walsh.Group, ℝ)) (f g : Lp K 1 haar) :
    product K q (f + g) = product K q f + product K q g := by
  apply Lp.ext
  filter_upwards [coeFn_product K q (f + g), coeFn_product K q f,
    coeFn_product K q g, Lp.coeFn_add f g, Lp.coeFn_add (product K q f) (product K q g)]
    with x hsum hf hg hadd hprod
  simp only [hsum, hprod, hf, hg, hadd, Pi.add_apply, smul_add]

theorem product_smul (q : C(Walsh.Group, ℝ)) (c : K) (f : Lp K 1 haar) :
    product K q (c • f) = c • product K q f := by
  apply Lp.ext
  filter_upwards [coeFn_product K q (c • f), coeFn_product K q f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (product K q f)] with x hcf hf hsm hprod
  simp only [hcf, hprod, hsm, Pi.smul_apply, hf]
  exact smul_comm (q x) c (f x)

theorem norm_product_le (q : C(Walsh.Group, ℝ)) (f : Lp K 1 haar) :
    ‖product K q f‖ ≤ ‖q‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_product K q f] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (q.norm_coe_le_norm x) (norm_nonneg _)

def multiplier (q : C(Walsh.Group, ℝ)) : Lp K 1 haar →L[K] Lp K 1 haar :=
  LinearMap.mkContinuous
    { toFun := product K q
      map_add' := product_add K q
      map_smul' := product_smul K q }
    ‖q‖ (norm_product_le K q)

theorem multiplier_apply (q : C(Walsh.Group, ℝ)) (f : Lp K 1 haar) :
    multiplier K q f = product K q f := rfl

theorem coeFn_multiplier (q : C(Walsh.Group, ℝ)) (f : Lp K 1 haar) :
    multiplier K q f =ᵐ[haar] fun x => q x • f x := coeFn_product K q f

theorem norm_multiplier_le (q : C(Walsh.Group, ℝ)) : ‖multiplier K q‖ ≤ ‖q‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg q) (norm_product_le K q)

def continuousProduct (q : C(Walsh.Group, ℝ)) (f : C(Walsh.Group, K)) :
    C(Walsh.Group, K) := ⟨fun x => q x • f x,
      Continuous.smul (M := ℝ) q.continuous f.continuous⟩

theorem multiplier_toLp (q : C(Walsh.Group, ℝ)) (f : C(Walsh.Group, K)) :
    multiplier K q (ContinuousMap.toLp 1 haar K f) =
      ContinuousMap.toLp 1 haar K (continuousProduct K q f) := by
  apply Lp.ext
  filter_upwards [coeFn_multiplier K q (ContinuousMap.toLp 1 haar K f),
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := K) haar f,
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := K) haar (continuousProduct K q f)]
    with x hx hf hprod
  rw [hx, hf, hprod]
  rfl

theorem multiplier_add (q r : C(Walsh.Group, ℝ)) :
    multiplier K (q + r) = multiplier K q + multiplier K r := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coeFn_multiplier K (q + r) f, coeFn_multiplier K q f,
    coeFn_multiplier K r f, Lp.coeFn_add (multiplier K q f) (multiplier K r f)]
    with x hsum hq hr hadd
  simp only [add_apply, hsum, hadd, hq, hr,
    ContinuousMap.add_apply, Pi.add_apply, add_smul]

theorem multiplier_one : multiplier K 1 = ContinuousLinearMap.id K (Lp K 1 haar) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coeFn_multiplier K 1 f] with x hx
  simpa only [ContinuousMap.one_apply, one_smul, ContinuousLinearMap.id_apply] using hx

theorem multiplier_sub (q r : C(Walsh.Group, ℝ)) (f : Lp K 1 haar) :
    multiplier K (q - r) f = multiplier K q f - multiplier K r f := by
  apply Lp.ext
  filter_upwards [coeFn_multiplier K (q - r) f, coeFn_multiplier K q f,
    coeFn_multiplier K r f, Lp.coeFn_sub (multiplier K q f) (multiplier K r f)]
    with x hsum hq hr hadd
  simp only [hsum, hadd, hq, hr, ContinuousMap.sub_apply, Pi.sub_apply, sub_smul]

end PL1.L1Multiplication
