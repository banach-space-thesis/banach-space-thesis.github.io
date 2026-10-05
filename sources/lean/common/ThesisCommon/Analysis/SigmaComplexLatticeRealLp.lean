import ThesisCommon.Analysis.SigmaComplexLatticeRealDual
import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.LpOnePair

/-! Real and imaginary coordinates give an actual real-linear Banach
isomorphism from complex ell-one to real ell-one on a doubled index set. -/
noncomputable section
namespace ThesisCommon
variable {I : Type*}

private theorem realPart_opNorm_le : ‖Complex.reCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by
    simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z)

private theorem imagPart_opNorm_le : ‖Complex.imCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by
    simpa only [Complex.imCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_im_le_norm z)

private theorem ofReal_opNorm_le : ‖Complex.ofRealCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun r => by simp)

def sigmaComplexLpRe : lp (fun _ : I => ℂ) 1 →L[ℝ] lp (fun _ : I => ℝ) 1 :=
  lpDiagonal 1 (fun _ => Complex.reCLM) 1 zero_le_one (fun _ => realPart_opNorm_le)

def sigmaComplexLpIm : lp (fun _ : I => ℂ) 1 →L[ℝ] lp (fun _ : I => ℝ) 1 :=
  lpDiagonal 1 (fun _ => Complex.imCLM) 1 zero_le_one (fun _ => imagPart_opNorm_le)

def sigmaComplexLpOfReal : lp (fun _ : I => ℝ) 1 →L[ℝ] lp (fun _ : I => ℂ) 1 :=
  lpDiagonal 1 (fun _ => Complex.ofRealCLM) 1 zero_le_one (fun _ => ofReal_opNorm_le)

@[simp] theorem sigmaComplexLpRe_apply (f : lp (fun _ : I => ℂ) 1) (i : I) :
    sigmaComplexLpRe f i = (f i).re := rfl

@[simp] theorem sigmaComplexLpIm_apply (f : lp (fun _ : I => ℂ) 1) (i : I) :
    sigmaComplexLpIm f i = (f i).im := rfl

@[simp] theorem sigmaComplexLpOfReal_apply (f : lp (fun _ : I => ℝ) 1) (i : I) :
    sigmaComplexLpOfReal f i = (f i : ℂ) := rfl

theorem sigmaComplexLpRe_norm_le (f : lp (fun _ : I => ℂ) 1) : ‖sigmaComplexLpRe f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using lp_norm_le_mul_of_pointwise f (sigmaComplexLpRe f) zero_le_one
    (fun i => by simpa only [sigmaComplexLpRe_apply, Real.norm_eq_abs, one_mul]
      using Complex.abs_re_le_norm (f i))

theorem sigmaComplexLpIm_norm_le (f : lp (fun _ : I => ℂ) 1) : ‖sigmaComplexLpIm f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using lp_norm_le_mul_of_pointwise f (sigmaComplexLpIm f) zero_le_one
    (fun i => by simpa only [sigmaComplexLpIm_apply, Real.norm_eq_abs, one_mul]
      using Complex.abs_im_le_norm (f i))

theorem sigmaComplexLpOfReal_norm_le (f : lp (fun _ : I => ℝ) 1) :
    ‖sigmaComplexLpOfReal f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using lp_norm_le_mul_of_pointwise f (sigmaComplexLpOfReal f) zero_le_one
    (fun i => by simp)

def sigmaComplexLpCombine (f : lp (fun _ : Bool × I => ℝ) 1) : lp (fun _ : I => ℂ) 1 :=
  sigmaComplexLpOfReal (lpOneComap ⟨fun i => (false,i),fun _ _ h => congrArg Prod.snd h⟩ f) +
    Complex.I • sigmaComplexLpOfReal
      (lpOneComap ⟨fun i => (true,i),fun _ _ h => congrArg Prod.snd h⟩ f)

@[simp] theorem sigmaComplexLpCombine_apply (f : lp (fun _ : Bool × I => ℝ) 1) (i : I) :
    sigmaComplexLpCombine f i = (f (false,i) : ℂ) + Complex.I * (f (true,i) : ℂ) := rfl

theorem sigmaComplexLpCombine_norm_le (f : lp (fun _ : Bool × I => ℝ) 1) :
    ‖sigmaComplexLpCombine f‖ ≤ 2 * ‖f‖ := by
  let e₀ : I ↪ Bool × I := ⟨fun i => (false,i),fun _ _ h => congrArg Prod.snd h⟩
  let e₁ : I ↪ Bool × I := ⟨fun i => (true,i),fun _ _ h => congrArg Prod.snd h⟩
  change ‖sigmaComplexLpOfReal (lpOneComap e₀ f) +
    Complex.I • sigmaComplexLpOfReal (lpOneComap e₁ f)‖ ≤ _
  calc
    _ ≤ ‖sigmaComplexLpOfReal (lpOneComap e₀ f)‖ +
        ‖Complex.I • sigmaComplexLpOfReal (lpOneComap e₁ f)‖ := norm_add_le _ _
    _ = ‖sigmaComplexLpOfReal (lpOneComap e₀ f)‖ +
        ‖sigmaComplexLpOfReal (lpOneComap e₁ f)‖ := by rw [norm_smul,Complex.norm_I,one_mul]
    _ ≤ ‖lpOneComap e₀ f‖ + ‖lpOneComap e₁ f‖ :=
      add_le_add (sigmaComplexLpOfReal_norm_le _) (sigmaComplexLpOfReal_norm_le _)
    _ ≤ 2 * ‖f‖ := by
      have h₀ := lpOneComap_norm_le e₀ f
      have h₁ := lpOneComap_norm_le e₁ f
      linarith

def sigmaComplexLpRealBoolEquiv (I : Type*) :
    lp (fun _ : I => ℂ) 1 ≃L[ℝ] lp (fun _ : Bool × I => ℝ) 1 := by
  let e : lp (fun _ : I => ℂ) 1 ≃ₗ[ℝ] lp (fun _ : Bool × I => ℝ) 1 :=
    { toFun := fun f => lpOnePair (sigmaComplexLpRe f) (sigmaComplexLpIm f)
      invFun := sigmaComplexLpCombine
      left_inv := by
        intro f
        apply lp.ext
        funext i
        apply Complex.ext <;> simp
      right_inv := by
        intro f
        apply lp.ext
        funext p
        rcases p with ⟨b,i⟩
        cases b <;> simp
      map_add' := by
        intro f g
        apply lp.ext
        funext p
        rcases p with ⟨b,i⟩
        cases b <;> simp
      map_smul' := by
        intro r f
        apply lp.ext
        funext p
        rcases p with ⟨b,i⟩
        cases b <;> simp }
  refine LinearEquiv.toContinuousLinearEquivOfBounds e 2 2 ?_ ?_
  · intro f
    change ‖lpOnePair (sigmaComplexLpRe f) (sigmaComplexLpIm f)‖ ≤ 2 * ‖f‖
    rw [lpOnePair_norm]
    have hre := sigmaComplexLpRe_norm_le f
    have him := sigmaComplexLpIm_norm_le f
    linarith
  · exact sigmaComplexLpCombine_norm_le

/-- The underlying real Banach space of complex ell-one is real ell-one on
`I × Bool`, with explicit mutually inverse real/imaginary coordinate maps. -/
def complexLpOneRealEquiv (I : Type*) :
    lp (fun _ : I => ℂ) 1 ≃L[ℝ] lp (fun _ : I × Bool => ℝ) 1 :=
  (sigmaComplexLpRealBoolEquiv I).trans
    (lpOneReindex (Equiv.prodComm I Bool)).toContinuousLinearEquiv

/-- A complex dual ell-one isomorphism gives an actual real dual ell-one
isomorphism, without any assumed representation of the underlying real space. -/
def complexDualLpOneRealEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (d : (E →L[ℂ] ℂ) ≃L[ℂ] lp (fun _ : I => ℂ) 1) :
    (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I × Bool => ℝ) 1 := by
  let dr : (E →L[ℂ] ℂ) ≃L[ℝ] lp (fun _ : I => ℂ) 1 :=
    LinearEquiv.toContinuousLinearEquivOfBounds (d.toLinearEquiv.restrictScalars ℝ)
      ‖d.toContinuousLinearMap‖ ‖d.symm.toContinuousLinearMap‖
      (fun x => d.toContinuousLinearMap.le_opNorm x)
      (fun y => d.symm.toContinuousLinearMap.le_opNorm y)
  exact (complexDualRealEquiv E).symm.toContinuousLinearEquiv.trans
    (dr.trans (complexLpOneRealEquiv I))

end ThesisCommon
