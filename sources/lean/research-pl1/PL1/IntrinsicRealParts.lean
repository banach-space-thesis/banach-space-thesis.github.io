import PL1.ScalarRealification
import PL1.IntrinsicWalsh

/-! # Actual real and imaginary coordinates of the scalar intrinsic graph -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace PL1.IntrinsicRealParts
open Walsh Noise IntrinsicGraph ScalarRealification ResolventEstimates

variable (K : Type*) [RCLike K]

def scalarPart (T : K →L[ℝ] ℝ) : Lp K 1 haar →L[ℝ] Lp ℝ 1 haar :=
  T.compLpL 1 haar

theorem scalarPart_convolution (T : K →L[ℝ] ℝ) (ν : Measure Walsh.Group)
    [IsProbabilityMeasure ν] (f : Lp K 1 haar) :
    scalarPart K T (convolutionL1 ν f) = convolutionL1 ν (scalarPart K T f) := by
  apply Lp.ext
  filter_upwards [T.coeFn_compLpL (convolutionL1 ν f), coeFn_convolutionL1 ν f,
    convolutionL1_ae_eq_integral_of_ae_eq ν (T.coeFn_compLpL f),
    (integrable_convolution_integrand ν f).prod_right_ae] with x hT hf hconv hint
  change (T.compLpL 1 haar (convolutionL1 ν f)) x = convolutionL1 ν (T.compLpL 1 haar f) x
  rw [hT, hf, hconv]
  exact (T.integral_comp_comm hint).symm

theorem scalarPart_analysis (T : K →L[ℝ] ℝ) (rates : ℕ → ℝ≥0)
    (n : ℕ) (f : Lp K 1 haar) :
    scalarPart K T ((dyadicSystem K rates).analysis n f) =
      (dyadicSystem ℝ rates).analysis n (scalarPart K T f) := by
  cases n with
  | zero => rfl
  | succ n =>
    let := isProbabilityMeasure_resolventMeasure rates (dyadicTime (n + 1)).property
    change scalarPart K T ((((dyadicRatio ^ (n + 1))⁻¹ : ℝ) : K) •
      (f - resolventL1 K rates (dyadicTime (n + 1)) f)) = _
    rw [← RCLike.real_smul_eq_coe_smul, map_smul, map_sub]
    rw [show resolventL1 K rates (dyadicTime (n + 1)) =
      convolutionL1 (resolventMeasure rates (dyadicTime (n + 1))) from rfl,
      scalarPart_convolution]
    rfl

theorem summable_norm_coords (rates : ℕ → ℝ≥0)
    (x : (dyadicSystem K rates).IntrinsicSpace) :
    Summable (fun n => ‖coord (dyadicSystem K rates).analysis n x‖) := by
  change Summable (fun n => ‖(x : lp (fun _ : ℕ => Lp K 1 haar) 1) n‖)
  simpa using (lp.memℓp (x : lp (fun _ : ℕ => Lp K 1 haar) 1)).summable
    (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal)

theorem summable_norm_parts (T : K →L[ℝ] ℝ) (rates : ℕ → ℝ≥0)
    (x : (dyadicSystem K rates).IntrinsicSpace) :
    Summable (fun n => ‖scalarPart K T (coord (dyadicSystem K rates).analysis n x)‖) := by
  have hs := summable_norm_coords K rates x
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => (scalarPart K T).le_opNorm (coord (dyadicSystem K rates).analysis n x))
    (hs.mul_left ‖scalarPart K T‖)

def partLinear (T : K →L[ℝ] ℝ) (rates : ℕ → ℝ≥0) :
    (dyadicSystem K rates).IntrinsicSpace →ₗ[ℝ] (dyadicSystem ℝ rates).IntrinsicSpace where
  toFun x := ⟨⟨fun n => scalarPart K T (coord (dyadicSystem K rates).analysis n x),
    memℓp_gen (by simpa using summable_norm_parts K T rates x)⟩, by
      intro n
      change scalarPart K T (coord (dyadicSystem K rates).analysis n x) = _
      rw [coord_eq, scalarPart_analysis]
      rfl⟩
  map_add' x y := by
    apply Subtype.ext
    apply lp.ext
    funext n
    change scalarPart K T (coord (dyadicSystem K rates).analysis n (x + y)) = _
    simp only [map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    apply lp.ext
    funext n
    simp only [RingHom.id_apply, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply]
    change scalarPart K T (coord (dyadicSystem K rates).analysis n (c • x)) =
      c • scalarPart K T (coord (dyadicSystem K rates).analysis n x)
    have hm : coord (dyadicSystem K rates).analysis n (c • x) =
        c • coord (dyadicSystem K rates).analysis n x := by
      exact ((coord (dyadicSystem K rates).analysis n).restrictScalars ℝ).map_smul c x
    exact (congrArg (scalarPart K T) hm).trans (map_smul (scalarPart K T) c _)

theorem coord_partLinear (T : K →L[ℝ] ℝ) (rates : ℕ → ℝ≥0)
    (n : ℕ) (x : (dyadicSystem K rates).IntrinsicSpace) :
    coord (dyadicSystem ℝ rates).analysis n (partLinear K T rates x) =
      scalarPart K T (coord (dyadicSystem K rates).analysis n x) := rfl

theorem norm_partLinear_le (T : K →L[ℝ] ℝ) (rates : ℕ → ℝ≥0)
    (x : (dyadicSystem K rates).IntrinsicSpace) :
    ‖partLinear K T rates x‖ ≤ ‖scalarPart K T‖ * ‖x‖ := by
  rw [IntrinsicGraph.norm_eq_tsum, IntrinsicGraph.norm_eq_tsum, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n => (scalarPart K T).le_opNorm _)
    (summable_norm_parts K T rates x)
    ((summable_norm_coords K rates x).mul_left ‖scalarPart K T‖)

def part (T : K →L[ℝ] ℝ) (rates : ℕ → ℝ≥0) :
    (dyadicSystem K rates).IntrinsicSpace →L[ℝ] (dyadicSystem ℝ rates).IntrinsicSpace :=
  (partLinear K T rates).mkContinuous ‖scalarPart K T‖ (norm_partLinear_le K T rates)

def realPart (rates : ℕ → ℝ≥0) := part K (@RCLike.reCLM K _) rates
def imagPart (rates : ℕ → ℝ≥0) := part K (@RCLike.imCLM K _) rates

def imL1 : Lp K 1 haar →L[ℝ] Lp ℝ 1 haar := scalarPart K (@RCLike.imCLM K _)

theorem coeFn_imL1 (f : Lp K 1 haar) :
    imL1 K f =ᵐ[haar] fun x => RCLike.im (f x) :=
  (@RCLike.imCLM K _).coeFn_compLpL f

@[simp] theorem coord_realPart (rates : ℕ → ℝ≥0) (n : ℕ)
    (x : (dyadicSystem K rates).IntrinsicSpace) :
    coord (dyadicSystem ℝ rates).analysis n (realPart K rates x) =
      reL1 K (coord (dyadicSystem K rates).analysis n x) := rfl

@[simp] theorem coord_imagPart (rates : ℕ → ℝ≥0) (n : ℕ)
    (x : (dyadicSystem K rates).IntrinsicSpace) :
    coord (dyadicSystem ℝ rates).analysis n (imagPart K rates x) =
      imL1 K (coord (dyadicSystem K rates).analysis n x) := rfl

theorem norm_ofRealL1_le (f : Lp ℝ 1 haar) : ‖ofRealL1 K f‖ ≤ ‖f‖ := by
  have h : ‖ofRealL1 K‖ ≤ 1 := by
    apply (ContinuousLinearMap.norm_compLpL_le (@RCLike.ofRealCLM K _)).trans
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [RCLike.ofRealCLM_apply, RCLike.norm_ofReal, Real.norm_eq_abs, one_mul, le_refl]
  exact ((ofRealL1 K).le_opNorm f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h (norm_nonneg f))

theorem re_add_im (f : Lp K 1 haar) :
    ofRealL1 K (reL1 K f) + (RCLike.I : K) • ofRealL1 K (imL1 K f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ofRealL1 K (reL1 K f))
      ((RCLike.I : K) • ofRealL1 K (imL1 K f)),
    Lp.coeFn_smul (RCLike.I : K) (ofRealL1 K (imL1 K f)),
    coeFn_ofRealL1 K (reL1 K f), coeFn_ofRealL1 K (imL1 K f),
    coeFn_reL1 K f, coeFn_imL1 K f] with x ha hs hor hoi hr hi
  rw [ha]
  change ofRealL1 K (reL1 K f) x +
    ((RCLike.I : K) • ofRealL1 K (imL1 K f)) x = f x
  rw [hs, hor]
  change (reL1 K f x : K) + (RCLike.I : K) * ofRealL1 K (imL1 K f) x = _
  rw [hoi, hr, hi, mul_comm RCLike.I, RCLike.re_add_im]

theorem norm_l1_le_parts (f : Lp K 1 haar) : ‖f‖ ≤ ‖reL1 K f‖ + ‖imL1 K f‖ := by
  have hI : ‖(RCLike.I : K)‖ ≤ 1 := by rw [RCLike.norm_I]; split_ifs <;> norm_num
  calc
    ‖f‖ = ‖ofRealL1 K (reL1 K f) + (RCLike.I : K) • ofRealL1 K (imL1 K f)‖ :=
      congrArg norm (re_add_im K f).symm
    _ ≤ ‖ofRealL1 K (reL1 K f)‖ + ‖(RCLike.I : K) • ofRealL1 K (imL1 K f)‖ := norm_add_le _ _
    _ ≤ ‖reL1 K f‖ + ‖imL1 K f‖ := by
      apply add_le_add (norm_ofRealL1_le K _)
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right hI (norm_nonneg _)).trans
        (by simpa using norm_ofRealL1_le K (imL1 K f))

/-- The scalar intrinsic norm is bounded by the sum of the two actual real
intrinsic norms. In particular the pair of real-part maps is injective. -/
theorem norm_le_parts (rates : ℕ → ℝ≥0) (x : (dyadicSystem K rates).IntrinsicSpace) :
    ‖x‖ ≤ ‖realPart K rates x‖ + ‖imagPart K rates x‖ := by
  rw [IntrinsicGraph.norm_eq_tsum, IntrinsicGraph.norm_eq_tsum,
    IntrinsicGraph.norm_eq_tsum]
  simp_rw [coord_realPart, coord_imagPart]
  change (∑' n, ‖coord (dyadicSystem K rates).analysis n x‖) ≤
    (∑' n, ‖scalarPart K (@RCLike.reCLM K _) (coord (dyadicSystem K rates).analysis n x)‖) +
    ∑' n, ‖scalarPart K (@RCLike.imCLM K _) (coord (dyadicSystem K rates).analysis n x)‖
  rw [← (summable_norm_parts K (@RCLike.reCLM K _) rates x).tsum_add
    (summable_norm_parts K (@RCLike.imCLM K _) rates x)]
  exact Summable.tsum_le_tsum (fun n => norm_l1_le_parts K _)
    (summable_norm_coords K rates x)
    ((summable_norm_parts K (@RCLike.reCLM K _) rates x).add
      (summable_norm_parts K (@RCLike.imCLM K _) rates x))

theorem parts_injective (rates : ℕ → ℝ≥0) :
    Function.Injective (fun x : (dyadicSystem K rates).IntrinsicSpace =>
      (realPart K rates x, imagPart K rates x)) := by
  intro x y h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hbound := norm_le_parts K rates (x - y)
  have hr : realPart K rates x = realPart K rates y := congrArg Prod.fst h
  have hi : imagPart K rates x = imagPart K rates y := congrArg Prod.snd h
  rw [map_sub, map_sub, hr, hi,
    sub_self, sub_self, norm_zero, add_zero] at hbound
  exact le_antisymm hbound (norm_nonneg _)

end PL1.IntrinsicRealParts
