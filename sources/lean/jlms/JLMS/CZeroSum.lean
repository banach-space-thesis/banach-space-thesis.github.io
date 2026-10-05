import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Dependent Banach c₀ sums

This is the Banach direct sum used by Kislyakov (1975), Section 1: families
whose coordinate norms vanish along the cofinite filter, with the supremum
norm. It is constructed as an actual closed submodule of mathlib's dependent
`lp E ∞`; in particular, no abstract direct-sum Banach structure is assumed.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace JLMS
universe u v w
variable (𝕜 : Type w) [RCLike 𝕜] {I : Type u} (E : I → Type v)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

def cZeroSumSubmodule : Submodule 𝕜 (lp E ∞) where
  carrier := {x | Tendsto (fun i => ‖x i‖) cofinite (𝓝 0)}
  zero_mem' := by
    change Tendsto (fun i => ‖(0 : lp E ∞) i‖) cofinite (𝓝 0)
    simpa only [lp.coeFn_zero, Pi.zero_apply, norm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℝ)) cofinite (𝓝 0))
  add_mem' := by
    intro x y hx hy
    apply squeeze_zero (fun i => norm_nonneg (x i + y i)) (fun i => norm_add_le (x i) (y i))
    simpa only [zero_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    change Tendsto (fun i => ‖c • x i‖) cofinite (𝓝 0)
    simpa only [norm_smul, mul_zero] using (tendsto_const_nhds (x := ‖c‖)).mul hx

abbrev CZeroSum := ↥(cZeroSumSubmodule 𝕜 E)

instance cZeroSumCoeFun : CoeFun (CZeroSum 𝕜 E) (fun _ => ∀ i, E i) :=
  ⟨fun x => x.val⟩

variable {𝕜 E}

namespace CZeroSum

@[ext] theorem ext {x y : CZeroSum 𝕜 E} (h : ∀ i, x i = y i) : x = y :=
  Subtype.ext (lp.ext (funext h))

@[simp] theorem zero_apply (i : I) : (0 : CZeroSum 𝕜 E) i = 0 := rfl
@[simp] theorem add_apply (x y : CZeroSum 𝕜 E) (i : I) : (x + y) i = x i + y i := rfl
@[simp] theorem sub_apply (x y : CZeroSum 𝕜 E) (i : I) : (x - y) i = x i - y i := rfl
@[simp] theorem smul_apply (c : 𝕜) (x : CZeroSum 𝕜 E) (i : I) : (c • x) i = c • x i := rfl

theorem norm_apply_le_norm (x : CZeroSum 𝕜 E) (i : I) : ‖x i‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x.val i

theorem norm_le {x : CZeroSum 𝕜 E} {C : ℝ} (hC : 0 ≤ C) (hx : ∀ i, ‖x i‖ ≤ C) :
    ‖x‖ ≤ C := lp.norm_le_of_forall_le hC hx

theorem tendsto_norm (x : CZeroSum 𝕜 E) : Tendsto (fun i => ‖x i‖) cofinite (𝓝 0) :=
  x.property

theorem finite_norm_ge (x : CZeroSum 𝕜 E) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {i | ε ≤ ‖x i‖} := by
  have h := (x.tendsto_norm.eventually (eventually_lt_nhds hε))
  simpa only [eventually_cofinite, not_lt] using h

end CZeroSum

theorem isClosed_cZeroSumSubmodule : IsClosed (cZeroSumSubmodule 𝕜 E : Set (lp E ∞)) := by
  apply isClosed_of_closure_subset
  intro f hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / 2) (half_pos hε)
  have htail : ∀ᶠ i in cofinite, ‖g i‖ < ε / 2 := hg.eventually
    (eventually_lt_nhds (half_pos hε))
  filter_upwards [htail] with i hi
  simp only [Real.dist_eq, sub_zero, abs_norm]
  have hcoord : ‖f i - g i‖ ≤ ‖f - g‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero (f - g) i
  have hbound : ‖f i‖ ≤ ‖f - g‖ + ‖g i‖ :=
    (norm_le_norm_sub_add (f i) (g i)).trans (add_le_add_right hcoord _)
  rw [dist_eq_norm] at hfg
  linarith

instance cZeroSumCompleteSpace [∀ i, CompleteSpace (E i)] : CompleteSpace (CZeroSum 𝕜 E) :=
  isClosed_cZeroSumSubmodule.completeSpace_coe

/-- A family with coordinate norms tending to zero defines a c₀ sum element;
boundedness follows from convergence along the cofinite filter. -/
def CZeroSum.mk (x : ∀ i, E i) (hx : Tendsto (fun i => ‖x i‖) cofinite (𝓝 0)) :
    CZeroSum 𝕜 E :=
  ⟨⟨x, memℓp_infty hx.bddAbove_range_of_cofinite⟩, hx⟩

@[simp] theorem CZeroSum.mk_apply (x : ∀ i, E i)
    (hx : Tendsto (fun i => ‖x i‖) cofinite (𝓝 0)) (i : I) :
    CZeroSum.mk (𝕜 := 𝕜) x hx i = x i := rfl

theorem tendsto_norm_cofinite_iff_finite (x : ∀ i, E i) :
    Tendsto (fun i => ‖x i‖) cofinite (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε → Set.Finite {i | ε ≤ ‖x i‖} := by
  constructor
  · intro hx ε hε
    have h := hx.eventually (eventually_lt_nhds hε)
    simpa only [eventually_cofinite, not_lt] using h
  · intro hx
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    simpa only [eventually_cofinite, Real.dist_eq, sub_zero, abs_norm, not_lt] using hx ε hε

end JLMS
