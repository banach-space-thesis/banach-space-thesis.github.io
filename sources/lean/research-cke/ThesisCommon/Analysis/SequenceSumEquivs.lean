import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.CZeroSingles
import ThesisCommon.Analysis.SequenceCoordinates

/-! Bounded isomorphisms needed in Pełczyński's decomposition argument.
All maps act on the actual sequence spaces. Products carry mathlib's maximum
norm; only bounded equivalence, not isometry with a finite-p product norm,
is claimed. Coordinatewise maps, finite product splitting, and head/tail
splitting work uniformly for every p ≥ 1 and for c₀.
-/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*}
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def lpMap (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : X →L[𝕜] Y) :
    lp (fun _ : ι => X) p →L[𝕜] lp (fun _ : ι => Y) p :=
  lpDiagonal p (fun _ => f) ‖f‖ (norm_nonneg f) (fun _ => le_rfl)

@[simp] theorem lpMap_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : X →L[𝕜] Y)
    (x : lp (fun _ : ι => X) p) (i : ι) : lpMap p f x i = f (x i) := rfl

def lpMapEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] (e : X ≃L[𝕜] Y) :
    lp (fun _ : ι => X) p ≃L[𝕜] lp (fun _ : ι => Y) p :=
  ContinuousLinearEquiv.equivOfInverse (lpMap p e.toContinuousLinearMap)
    (lpMap p e.symm.toContinuousLinearMap)
    (by intro x; ext i; exact e.symm_apply_apply (x i))
    (by intro x; ext i; exact e.apply_symm_apply (x i))

def lpProdEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    lp (fun _ : ι => X × Y) p ≃L[𝕜]
      lp (fun _ : ι => X) p × lp (fun _ : ι => Y) p :=
  ContinuousLinearEquiv.equivOfInverse
    ((lpMap p (ContinuousLinearMap.fst 𝕜 X Y)).prod
      (lpMap p (ContinuousLinearMap.snd 𝕜 X Y)))
    ((lpMap p (ContinuousLinearMap.inl 𝕜 X Y)).coprod
      (lpMap p (ContinuousLinearMap.inr 𝕜 X Y)))
    (by intro x; ext i <;> simp [lpMap_apply])
    (by intro x; apply Prod.ext <;> ext i <;> simp [lpMap_apply])

variable [TopologicalSpace ι] [DiscreteTopology ι]

def cZeroMap (f : X →L[𝕜] Y) : C₀(ι, X) →L[𝕜] C₀(ι, Y) :=
  cZeroDiagonal (fun _ => f) ‖f‖ (norm_nonneg f) (fun _ => le_rfl)

@[simp] theorem cZeroMap_apply (f : X →L[𝕜] Y) (x : C₀(ι, X)) (i : ι) :
    cZeroMap f x i = f (x i) := rfl

def cZeroMapEquiv (e : X ≃L[𝕜] Y) : C₀(ι, X) ≃L[𝕜] C₀(ι, Y) :=
  ContinuousLinearEquiv.equivOfInverse (cZeroMap e.toContinuousLinearMap)
    (cZeroMap e.symm.toContinuousLinearMap)
    (by intro x; ext i; exact e.symm_apply_apply (x i))
    (by intro x; ext i; exact e.apply_symm_apply (x i))

def cZeroProdEquiv : C₀(ι, X × Y) ≃L[𝕜] C₀(ι, X) × C₀(ι, Y) :=
  ContinuousLinearEquiv.equivOfInverse
    ((cZeroMap (ContinuousLinearMap.fst 𝕜 X Y)).prod
      (cZeroMap (ContinuousLinearMap.snd 𝕜 X Y)))
    ((cZeroMap (ContinuousLinearMap.inl 𝕜 X Y)).coprod
      (cZeroMap (ContinuousLinearMap.inr 𝕜 X Y)))
    (by intro x; ext i <;> simp [cZeroMap_apply])
    (by intro x; apply Prod.ext <;> ext i <;> simp [cZeroMap_apply])

/-- The injection retaining all coordinates after the first. -/
def sequenceSuccessor : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩

@[simp] theorem lpExtend_sequenceSuccessor_zero (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (x : lp (fun _ : ℕ => X) p) : lpExtend (𝕜 := 𝕜) p sequenceSuccessor x 0 = 0 := by
  change Function.extend sequenceSuccessor x 0 0 = 0
  exact Function.extend_apply' _ _ _ (by simp [sequenceSuccessor])

@[simp] theorem cZeroExtend_sequenceSuccessor_zero (x : CZeroSum X) :
    cZeroExtend (𝕜 := 𝕜) sequenceSuccessor x 0 = 0 := by
  change Function.extend sequenceSuccessor x 0 0 = 0
  exact Function.extend_apply' _ _ _ (by simp [sequenceSuccessor])

/-- Split off the first coordinate of ℓp, retaining bounded inverse maps. -/
def lpHeadTailEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    lp (fun _ : ℕ => X) p ≃L[𝕜] X × lp (fun _ : ℕ => X) p :=
  ContinuousLinearEquiv.equivOfInverse
    ((lpCoordinate p 0).prod (lpRestrict p sequenceSuccessor))
    ((lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p 0).coprod
      (lpExtend p sequenceSuccessor))
    (by
      intro x
      ext n
      cases n with
      | zero => simp
      | succ n =>
        change lp.single (E := fun _ : ℕ => X) p 0 (x 0) (n+1) +
          lpExtend (𝕜 := 𝕜) p sequenceSuccessor
            (lpRestrict (𝕜 := 𝕜) p sequenceSuccessor x) (sequenceSuccessor n) = x (n+1)
        rw [lpExtend_apply_image]
        simp [lpRestrict_apply, sequenceSuccessor])
    (by
      intro x
      apply Prod.ext
      · simp
      · ext n
        change lp.single (E := fun _ : ℕ => X) p 0 x.1 (n+1) +
          lpExtend (𝕜 := 𝕜) p sequenceSuccessor x.2 (sequenceSuccessor n) = x.2 n
        rw [lpExtend_apply_image]
        simp)

/-- The same head/tail isomorphism on the actual null-sequence space. -/
def cZeroHeadTailEquiv : CZeroSum X ≃L[𝕜] X × CZeroSum X :=
  ContinuousLinearEquiv.equivOfInverse
    ((cZeroCoordinate 0).prod (cZeroRestrict sequenceSuccessor))
    ((cZeroSingleCLM 0).coprod (cZeroExtend sequenceSuccessor))
    (by
      intro x
      ext n
      cases n with
      | zero => simp
      | succ n =>
        change cZeroSingle 0 (x 0) (n+1) +
          cZeroExtend (𝕜 := 𝕜) sequenceSuccessor
            (cZeroRestrict (𝕜 := 𝕜) sequenceSuccessor x) (sequenceSuccessor n) = x (n+1)
        rw [cZeroExtend_apply_image]
        simp [cZeroRestrict_apply, sequenceSuccessor, cZeroSingle])
    (by
      intro x
      apply Prod.ext
      · simp
      · ext n
        change cZeroSingle 0 x.1 (n+1) +
          cZeroExtend (𝕜 := 𝕜) sequenceSuccessor x.2 (sequenceSuccessor n) = x.2 n
        simp [cZeroSingle])

end ThesisCommon
