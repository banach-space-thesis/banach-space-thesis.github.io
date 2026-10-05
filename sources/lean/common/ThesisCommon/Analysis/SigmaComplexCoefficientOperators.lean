import ThesisCommon.Analysis.LpOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Complex ℓ¹ coordinate reindexing and disjoint sums. -/
noncomputable section
namespace ThesisCommon

theorem complexLpOneHasSumNorm {ι : Type*} (f : lp (fun _ : ι => ℂ) 1) :
    HasSum (fun i => ‖f i‖) ‖f‖ := by
  simpa only [ENNReal.toReal_one,Real.rpow_one] using
    lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) f

def complexLpOneReindex {ι κ : Type*} (e : ι ≃ κ) :
    lp (fun _ : κ => ℂ) 1 ≃ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 1 where
  toFun := lpRestrict (𝕜 := ℂ) 1 e.toEmbedding
  invFun := lpRestrict (𝕜 := ℂ) 1 e.symm.toEmbedding
  left_inv f := by apply lp.ext; funext i; simp
  right_inv f := by apply lp.ext; funext i; simp
  map_add' _ _ := by apply lp.ext; rfl
  map_smul' _ _ := by apply lp.ext; rfl
  norm_map' f := by
    rw [← (complexLpOneHasSumNorm _).tsum_eq,← (complexLpOneHasSumNorm f).tsum_eq]
    exact e.tsum_eq (fun i => ‖f i‖)

@[simp] theorem complexLpOneReindex_apply {ι κ : Type*} (e : ι ≃ κ)
    (f : lp (fun _ : κ => ℂ) 1) (i : ι) : complexLpOneReindex e f i = f (e i) := rfl

theorem complexLpOneSum_hasSum_norm {ι κ : Type*}
    (f : lp (fun _ : ι => ℂ) 1) (g : lp (fun _ : κ => ℂ) 1) :
    HasSum (fun p : ι ⊕ κ => ‖Sum.elim f g p‖) (‖f‖ + ‖g‖) :=
  HasSum.sum (f := fun p : ι ⊕ κ => ‖Sum.elim f g p‖)
    (complexLpOneHasSumNorm f) (complexLpOneHasSumNorm g)

def complexLpOneSum {ι κ : Type*}
    (f : lp (fun _ : ι => ℂ) 1) (g : lp (fun _ : κ => ℂ) 1) :
    lp (fun _ : ι ⊕ κ => ℂ) 1 :=
  ⟨Sum.elim f g,memℓp_gen (by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using (complexLpOneSum_hasSum_norm f g).summable)⟩

@[simp] theorem complexLpOneSum_apply_left {ι κ : Type*}
    (f : lp (fun _ : ι => ℂ) 1) (g : lp (fun _ : κ => ℂ) 1) (i : ι) :
    complexLpOneSum f g (.inl i) = f i := rfl

@[simp] theorem complexLpOneSum_apply_right {ι κ : Type*}
    (f : lp (fun _ : ι => ℂ) 1) (g : lp (fun _ : κ => ℂ) 1) (i : κ) :
    complexLpOneSum f g (.inr i) = g i := rfl

@[simp] theorem complexLpOneSum_norm {ι κ : Type*}
    (f : lp (fun _ : ι => ℂ) 1) (g : lp (fun _ : κ => ℂ) 1) :
    ‖complexLpOneSum f g‖ = ‖f‖ + ‖g‖ :=
  (complexLpOneHasSumNorm (complexLpOneSum f g)).unique (complexLpOneSum_hasSum_norm f g)

def complexLpOnePair {ι : Type*} (f g : lp (fun _ : ι => ℂ) 1) :
    lp (fun _ : Bool × ι => ℂ) 1 :=
  complexLpOneReindex (Equiv.boolProdEquivSum ι) (complexLpOneSum f g)

@[simp] theorem complexLpOnePair_false {ι : Type*} (f g : lp (fun _ : ι => ℂ) 1) (i : ι) :
    complexLpOnePair f g (false,i) = f i := rfl

@[simp] theorem complexLpOnePair_true {ι : Type*} (f g : lp (fun _ : ι => ℂ) 1) (i : ι) :
    complexLpOnePair f g (true,i) = g i := rfl

@[simp] theorem complexLpOnePair_norm {ι : Type*} (f g : lp (fun _ : ι => ℂ) 1) :
    ‖complexLpOnePair f g‖ = ‖f‖ + ‖g‖ := by
  rw [complexLpOnePair,LinearIsometryEquiv.norm_map,complexLpOneSum_norm]

end ThesisCommon

