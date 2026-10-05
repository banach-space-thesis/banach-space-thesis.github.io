import Sigma.ComplexSplitting
import Sigma.ContinuousRepresentation

/-! The complex closed span is isometric to the complex continuous functions
on its Mrówka compactification. Real and imaginary parts reduce the density
step to the existing real representation; the scalar field of the result is ℂ. -/
noncomputable section
open Set Topology
namespace SigmaNonprimarity

def complexAmbientOfReal : Ambient →L[ℝ] ComplexAmbient :=
  Complex.ofRealCLM.compLeftContinuousBounded Point

@[simp] theorem complexAmbientOfReal_apply (f : Ambient) (p : Point) :
    complexAmbientOfReal f p = (f p : ℂ) := rfl

@[simp] theorem complexAmbientOfReal_characteristic (A : Set Point) :
    complexAmbientOfReal (characteristic A) = complexCharacteristic A := by
  classical
  ext p
  by_cases hp : p ∈ A <;> simp [hp]

theorem complexAmbientOfReal_mem {B : Set (Set Point)} {f : Ambient} (hf : f ∈ JL B) :
    complexAmbientOfReal f ∈ ComplexJL B := by
  have hle : JL B ≤ ((ComplexJL B).restrictScalars ℝ).comap
      complexAmbientOfReal.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro g hg
      change complexAmbientOfReal g ∈ ComplexJL B
      rcases hg with (⟨p,rfl⟩ | ⟨b,hb,rfl⟩) | rfl
      · rw [complexAmbientOfReal_characteristic]
        exact complexCharacteristic_singleton_mem_ComplexJL _ _
      · rw [complexAmbientOfReal_characteristic]
        exact complexCharacteristic_mem_ComplexJL hb
      · rw [complexAmbientOfReal_characteristic]
        exact complexConstant_mem_ComplexJL _
    · exact (Submodule.isClosed_topologicalClosure _).preimage complexAmbientOfReal.continuous
  exact hle hf

def complexRestrictToBase (B : Set (Set Point)) :
    C(AUCompactum B,ℂ) →ₐ[ℂ] ComplexAmbient where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p => f (↑(Sum.inl p : MrowkaBase B))) ‖f‖ (fun _ => f.norm_coe_le_norm _)
  map_zero' := by ext p; rfl
  map_one' := by ext p; rfl
  map_add' := by intros; ext p; rfl
  map_mul' := by intros; ext p; rfl
  commutes' := by intro r; ext p; rfl

@[simp] theorem complexRestrictToBase_apply (B : Set (Set Point))
    (f : C(AUCompactum B,ℂ)) (p : Point) :
    complexRestrictToBase B f p = f (↑(Sum.inl p : MrowkaBase B)) := rfl

theorem complexRestrictToBase_norm_le (B : Set (Set Point)) (f : C(AUCompactum B,ℂ)) :
    ‖complexRestrictToBase B f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (fun p => f.norm_coe_le_norm _)

def complexRestrictToBaseCLM (B : Set (Set Point)) :
    C(AUCompactum B,ℂ) →L[ℂ] ComplexAmbient :=
  (complexRestrictToBase B).toLinearMap.mkContinuous 1
    (by intro f; simpa using complexRestrictToBase_norm_le B f)

theorem complexRestrictToBase_norm {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (f : C(AUCompactum B,ℂ)) :
    ‖complexRestrictToBase B f‖ = ‖f‖ := by
  apply le_antisymm (complexRestrictToBase_norm_le B f)
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  exact (compactumBaseDense hB hInf).induction_on x
    (isClosed_le f.continuous.norm continuous_const)
    (fun p => (complexRestrictToBase B f).norm_coe_le_norm p)

def complexRestrictToBaseIsometry {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    C(AUCompactum B,ℂ) →ₗᵢ[ℂ] ComplexAmbient where
  toLinearMap := (complexRestrictToBase B).toLinearMap
  norm_map' := complexRestrictToBase_norm hB hInf

def complexLiftRealContinuous {K : Type*} [TopologicalSpace K]
    (f : C(K,ℝ)) : C(K,ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem complexRestrict_lift_real (B : Set (Set Point)) (f : C(AUCompactum B,ℝ)) :
    complexRestrictToBase B (complexLiftRealContinuous f) =
      complexAmbientOfReal (restrictToBase B f) := rfl

theorem complexJL_le_restriction_range {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    ComplexJL B ≤ LinearMap.range (complexRestrictToBase B).toLinearMap := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    intro f hf
    rcases hf with (⟨p,rfl⟩ | ⟨b,hb,rfl⟩) | rfl
    · refine ⟨complexLiftRealContinuous (singletonFunction hB p),?_⟩
      change complexRestrictToBase B _ = _
      rw [complexRestrict_lift_real,restrict_singletonFunction,complexAmbientOfReal_characteristic]
    · refine ⟨complexLiftRealContinuous (tailFunction hB ⟨b,hb⟩),?_⟩
      change complexRestrictToBase B _ = _
      rw [complexRestrict_lift_real,restrict_tailFunction,complexAmbientOfReal_characteristic]
    · refine ⟨complexLiftRealContinuous 1,?_⟩
      change complexRestrictToBase B _ = _
      rw [complexRestrict_lift_real,show restrictToBase B 1 = characteristic Set.univ from by
        ext p; simp,complexAmbientOfReal_characteristic]
  · exact (complexRestrictToBaseIsometry hB hInf).isometry.isClosedEmbedding.isClosed_range

theorem complexRestrictToBase_mem {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (f : C(AUCompactum B,ℂ)) : complexRestrictToBase B f ∈ ComplexJL B := by
  let fr : C(AUCompactum B,ℝ) := ⟨fun x => (f x).re,Complex.continuous_re.comp f.continuous⟩
  let fi : C(AUCompactum B,ℝ) := ⟨fun x => (f x).im,Complex.continuous_im.comp f.continuous⟩
  have hr := complexAmbientOfReal_mem (restrictToBase_mem_JL hB fr)
  have hi := complexAmbientOfReal_mem (restrictToBase_mem_JL hB fi)
  have hd : complexRestrictToBase B f = complexAmbientOfReal (restrictToBase B fr) +
      Complex.I • complexAmbientOfReal (restrictToBase B fi) := by
    ext p
    change f _ = ((f _).re : ℂ) + Complex.I * ((f _).im : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  rw [hd]
  exact (ComplexJL B).add_mem hr ((ComplexJL B).smul_mem Complex.I hi)

def complexJLContinuousEquiv {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    ComplexJL B ≃ₗᵢ[ℂ] C(AUCompactum B,ℂ) := by
  let e : C(AUCompactum B,ℂ) →ₗᵢ[ℂ] ComplexJL B :=
    { toLinearMap := (complexRestrictToBase B).toLinearMap.codRestrict
        (ComplexJL B) (complexRestrictToBase_mem hB)
      norm_map' := complexRestrictToBase_norm hB hInf }
  refine (LinearIsometryEquiv.ofSurjective e ?_).symm
  intro f
  obtain ⟨g,hg⟩ := complexJL_le_restriction_range hB hInf f.property
  exact ⟨g,Subtype.ext hg⟩

@[simp] theorem complexJLContinuousEquiv_symm_apply {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (f : C(AUCompactum B,ℂ)) :
    ((complexJLContinuousEquiv hB hInf).symm f).val = complexRestrictToBase B f := rfl

theorem complexJLContinuousEquiv_restrict {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (f : C(AUCompactum B,ℂ))
    (hf : complexRestrictToBase B f ∈ ComplexJL B) :
    complexJLContinuousEquiv hB hInf ⟨complexRestrictToBase B f,hf⟩ = f :=
  (complexJLContinuousEquiv hB hInf).apply_symm_apply f

end SigmaNonprimarity

