import ThesisCommon.Analysis.LpOneReindex
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Logic.Equiv.Prod

/-! Joining two coefficient vectors on disjoint copies adds their ell-one norms. -/
noncomputable section
namespace ThesisCommon

theorem lpOneSum_hasSum_norm {ι κ : Type*}
    (f : lp (fun _ : ι => ℝ) 1) (g : lp (fun _ : κ => ℝ) 1) :
    HasSum (fun p : ι ⊕ κ => ‖Sum.elim f g p‖) (‖f‖ + ‖g‖) :=
  (lp_one_hasSum_norm f).sum (lp_one_hasSum_norm g)

def lpOneSum {ι κ : Type*} (f : lp (fun _ : ι => ℝ) 1) (g : lp (fun _ : κ => ℝ) 1) :
    lp (fun _ : ι ⊕ κ => ℝ) 1 :=
  ⟨Sum.elim f g, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using (lpOneSum_hasSum_norm f g).summable)⟩

@[simp] theorem lpOneSum_apply_left {ι κ : Type*}
    (f : lp (fun _ : ι => ℝ) 1) (g : lp (fun _ : κ => ℝ) 1) (i : ι) :
    lpOneSum f g (.inl i) = f i := rfl

@[simp] theorem lpOneSum_apply_right {ι κ : Type*}
    (f : lp (fun _ : ι => ℝ) 1) (g : lp (fun _ : κ => ℝ) 1) (i : κ) :
    lpOneSum f g (.inr i) = g i := rfl

@[simp] theorem lpOneSum_norm {ι κ : Type*}
    (f : lp (fun _ : ι => ℝ) 1) (g : lp (fun _ : κ => ℝ) 1) :
    ‖lpOneSum f g‖ = ‖f‖ + ‖g‖ :=
  (lp_one_hasSum_norm (lpOneSum f g)).unique (lpOneSum_hasSum_norm f g)

def lpOnePair {ι : Type*} (f g : lp (fun _ : ι => ℝ) 1) : lp (fun _ : Bool × ι => ℝ) 1 :=
  lpOneReindex (Equiv.boolProdEquivSum ι) (lpOneSum f g)

@[simp] theorem lpOnePair_false {ι : Type*} (f g : lp (fun _ : ι => ℝ) 1) (i : ι) :
    lpOnePair f g (false,i) = f i := rfl

@[simp] theorem lpOnePair_true {ι : Type*} (f g : lp (fun _ : ι => ℝ) 1) (i : ι) :
    lpOnePair f g (true,i) = g i := rfl

@[simp] theorem lpOnePair_norm {ι : Type*} (f g : lp (fun _ : ι => ℝ) 1) :
    ‖lpOnePair f g‖ = ‖f‖ + ‖g‖ := by
  rw [lpOnePair, LinearIsometryEquiv.norm_map, lpOneSum_norm]

end ThesisCommon
