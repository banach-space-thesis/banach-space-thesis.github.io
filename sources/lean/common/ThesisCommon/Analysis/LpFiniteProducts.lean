import ThesisCommon.Analysis.SequenceSumEquivs
import Mathlib.Logic.Denumerable

/-! Finite products and finite coefficient spaces in the actual lp norms.
All maps are bounded linear maps; no equality between the maximum norm and
a finite-p norm is assumed. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {ι κ : Type*}
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def lpReindexEquiv (e : ι ≃ κ) :
    lp (fun _ : κ => X) p ≃L[𝕜] lp (fun _ : ι => X) p :=
  ContinuousLinearEquiv.equivOfInverse
    (lpRestrict p e.toEmbedding) (lpRestrict p e.symm.toEmbedding)
    (by intro x; ext i; change x (e (e.symm i)) = x i; rw [e.apply_symm_apply])
    (by intro x; ext i; change x (e.symm (e i)) = x i; rw [e.symm_apply_apply])

def lpFinitePiRead [Fintype κ] :
    lp (fun _ : ι => κ → X) p →L[𝕜] (κ → lp (fun _ : ι => X) p) :=
  ContinuousLinearMap.pi (fun k => lpMap p (ContinuousLinearMap.proj k))

def lpFinitePiInsert [Fintype κ] :
    (κ → lp (fun _ : ι => X) p) →L[𝕜] lp (fun _ : ι => κ → X) p := by
  classical
  exact ∑ k, (lpMap p (ContinuousLinearMap.single 𝕜 (fun _ : κ => X) k)).comp
    (ContinuousLinearMap.proj k)

@[simp] theorem lpFinitePiRead_apply [Fintype κ]
    (x : lp (fun _ : ι => κ → X) p) (k : κ) (i : ι) :
    lpFinitePiRead (𝕜 := 𝕜) p x k i = x i k := rfl

@[simp] theorem lpFinitePiInsert_apply [Fintype κ]
    (x : κ → lp (fun _ : ι => X) p) (i : ι) (k : κ) :
    lpFinitePiInsert (𝕜 := 𝕜) p x i k = x k i := by
  classical
  simp [lpFinitePiInsert, lpMap_apply, ContinuousLinearMap.single_apply,
    lp.coeFn_sum, Finset.sum_apply]

def lpFinitePiEquiv [Fintype κ] :
    lp (fun _ : ι => κ → X) p ≃L[𝕜] (κ → lp (fun _ : ι => X) p) :=
  ContinuousLinearEquiv.equivOfInverse (lpFinitePiRead p) (lpFinitePiInsert p)
    (by intro x; ext i k; simp)
    (by intro x; funext k; ext i; simp)

def lpProductIndex (k : κ) : ι ↪ κ × ι :=
  ⟨fun i => (k, i), fun _ _ h => (Prod.mk.inj h).2⟩

def lpProductRead [Fintype κ] :
    lp (fun _ : κ × ι => X) p →L[𝕜] (κ → lp (fun _ : ι => X) p) :=
  ContinuousLinearMap.pi (fun k => lpRestrict p (lpProductIndex k))

def lpProductInsert [Fintype κ] :
    (κ → lp (fun _ : ι => X) p) →L[𝕜] lp (fun _ : κ × ι => X) p :=
  ∑ k, (lpExtend p (lpProductIndex k)).comp (ContinuousLinearMap.proj k)

theorem lpExtend_productIndex_apply [DecidableEq κ] (j k : κ) (x : lp (fun _ : ι => X) p) (i : ι) :
    lpExtend (𝕜 := 𝕜) p (lpProductIndex j) x (k, i) = if j = k then x i else 0 := by
  classical
  by_cases h : j = k
  · subst k
    simpa only [if_true] using lpExtend_apply_image (𝕜 := 𝕜) (lpProductIndex j) x i
  · change Function.extend (lpProductIndex j) x 0 (k, i) = _
    rw [Function.extend_apply' _ _ _ (by
      rintro ⟨a, ha⟩
      exact h (Prod.mk.inj ha).1), if_neg h]
    rfl

@[simp] theorem lpProductRead_apply [Fintype κ]
    (x : lp (fun _ : κ × ι => X) p) (k : κ) (i : ι) :
    lpProductRead (𝕜 := 𝕜) p x k i = x (k, i) := rfl

@[simp] theorem lpProductInsert_apply [Fintype κ]
    (x : κ → lp (fun _ : ι => X) p) (k : κ) (i : ι) :
    lpProductInsert (𝕜 := 𝕜) p x (k, i) = x k i := by
  classical
  simp [lpProductInsert, lp.coeFn_sum, lpExtend_productIndex_apply]

def lpProductIndexEquiv [Fintype κ] :
    lp (fun _ : κ × ι => X) p ≃L[𝕜] (κ → lp (fun _ : ι => X) p) :=
  ContinuousLinearEquiv.equivOfInverse (lpProductRead p) (lpProductInsert p)
    (by intro x; ext ⟨k, i⟩; simp)
    (by intro x; funext k; ext i; simp)

def lpCountableFinitePiCoefficientEquiv [Fintype κ] [Nonempty κ] :
    lp (fun _ : ℕ => κ → X) p ≃L[𝕜] lp (fun _ : ℕ => X) p :=
  (lpFinitePiEquiv p).trans ((lpProductIndexEquiv p).symm.trans
    (lpReindexEquiv p (Classical.choice (inferInstance : Nonempty (ℕ ≃ κ × ℕ)))))

end ThesisCommon

