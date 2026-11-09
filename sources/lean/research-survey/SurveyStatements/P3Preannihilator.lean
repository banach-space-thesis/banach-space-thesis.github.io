import SurveyStatements.P3Basic

/-! The quotient geometry used after preadjoint extraction in Problem 3.
All results in this module are proved without assuming the main theorem. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SurveyStatements.P3

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The preannihilator consists of vectors killed by every functional in `E`. -/
def preannihilator (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) : Submodule 𝕜 X :=
  ⨅ f : E, LinearMap.ker f.val

@[simp] theorem mem_preannihilator (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) (x : X) :
    x ∈ preannihilator E ↔ ∀ f : E, f.val x = 0 := by
  simp only [preannihilator, Submodule.mem_iInf, LinearMap.mem_ker]

instance preannihilator_closed (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) :
    IsClosed (preannihilator E : Set X) := by
  rw [preannihilator, Submodule.coe_iInf]
  exact isClosed_iInter (fun f => ContinuousLinearMap.isClosed_ker f.val)

/-- A functional in `E` descends to the quotient by `E`'s preannihilator. -/
def preannihilatorLift (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) (f : E) :
    (X ⧸ preannihilator E) →L[𝕜] 𝕜 :=
  let L := (preannihilator E).liftQ f.val.toLinearMap
    (fun x hx => (mem_preannihilator E x).mp hx f)
  L.mkContinuous ‖f.val‖ (quotient_norm_bound _ L (norm_nonneg _)
    (fun x => f.val.le_opNorm x))

@[simp] theorem preannihilatorLift_apply (E : Submodule 𝕜 (X →L[𝕜] 𝕜))
    (f : E) (x : X) :
    preannihilatorLift E f (quotientMap (preannihilator E) x) = f.val x := rfl

@[simp] theorem norm_preannihilatorLift (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) (f : E) :
    ‖preannihilatorLift E f‖ = ‖f.val‖ := by
  have h : adjoint (quotientMap (preannihilator E)) (preannihilatorLift E f) = f.val := by
    ext x
    rfl
  calc
    ‖preannihilatorLift E f‖ =
        ‖adjoint (quotientMap (preannihilator E)) (preannihilatorLift E f)‖ :=
      (norm_adjoint_quotientMap _ _).symm
    _ = ‖f.val‖ := congrArg norm h

/-- The canonical isometric inclusion `J : E → (X / E⊥)*` used by the source. -/
def preannihilatorDualEmbedding (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) :
    E →ₗᵢ[𝕜] ((X ⧸ preannihilator E) →L[𝕜] 𝕜) where
  toFun := preannihilatorLift E
  map_add' f g := by
    ext z
    obtain ⟨x, rfl⟩ := (preannihilator E).mkQ_surjective z
    rfl
  map_smul' c f := by
    ext z
    obtain ⟨x, rfl⟩ := (preannihilator E).mkQ_surjective z
    rfl
  norm_map' := norm_preannihilatorLift E

/-- An infinite-dimensional family of functionals forces its preannihilator
to have infinite codimension. -/
theorem preannihilator_quotient_infiniteDimensional
    (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E) :
    ¬ FiniteDimensional 𝕜 (X ⧸ preannihilator E) := by
  intro hQ
  letI := hQ
  letI : FiniteDimensional 𝕜 ((X ⧸ preannihilator E) →L[𝕜] 𝕜) :=
    FiniteDimensional.of_injective (V₂ := (X ⧸ preannihilator E) →ₗ[𝕜] 𝕜)
      (ContinuousLinearMap.coeLM 𝕜)
      ContinuousLinearMap.coe_injective
  exact hE (FiniteDimensional.of_injective
    (V₂ := (X ⧸ preannihilator E) →L[𝕜] 𝕜)
    (preannihilatorDualEmbedding E).toLinearMap
    (by
      intro f g hfg
      apply Subtype.ext
      ext x
      exact congrArg (fun p : (X ⧸ preannihilator E) →L[𝕜] 𝕜 =>
        p (quotientMap (preannihilator E) x)) hfg))

/-- These descended functionals separate the quotient, directly by its
definition. No weak-star density argument is needed for this step. -/
theorem quotient_eq_zero_of_preannihilatorLift_eq_zero
    (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) (z : X ⧸ preannihilator E)
    (hz : ∀ f : E, preannihilatorLift E f z = 0) : z = 0 := by
  obtain ⟨x, rfl⟩ := (preannihilator E).mkQ_surjective z
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (mem_preannihilator E x).mpr hz

/-- The pairing identity obtained from extraction already implies the exact
operator factorization in the source. -/
theorem factorization_of_preannihilator_pairing
    (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) (T : X →L[𝕜] Y)
    (A : Y →L[𝕜] (X ⧸ preannihilator E))
    (h : ∀ (f : E) (x : X), preannihilatorLift E f (A (T x)) = f.val x) :
    A.comp T = quotientMap (preannihilator E) := by
  ext x
  apply sub_eq_zero.mp
  apply quotient_eq_zero_of_preannihilatorLift_eq_zero E
  intro f
  rw [map_sub, preannihilatorLift_apply, ContinuousLinearMap.comp_apply, h, sub_self]

/-- Once the preadjoint extraction supplies its pairing identity, all remaining
quotient and dimension steps in the hard implication are formal consequences. -/
theorem not_strictlyCosingular_of_preannihilator_pairing
    (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) (hE : ¬ FiniteDimensional 𝕜 E)
    (T : X →L[𝕜] Y) (A : Y →L[𝕜] (X ⧸ preannihilator E))
    (h : ∀ (f : E) (x : X), preannihilatorLift E f (A (T x)) = f.val x) :
    ¬ IsStrictlyCosingular T := by
  apply not_strictlyCosingular_of_quotient_factorization T A
    (quotientMap (preannihilator E))
    (preannihilator_quotient_infiniteDimensional E hE)
    (preannihilator E).mkQ_surjective
  exact factorization_of_preannihilator_pairing E T A h

end SurveyStatements.P3
