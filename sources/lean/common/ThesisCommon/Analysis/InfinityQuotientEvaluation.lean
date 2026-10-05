import ThesisCommon.Analysis.InfinityCZeroQuotient
import ThesisCommon.Analysis.QuotientContractions
import ThesisCommon.Analysis.ScalarUltralimit

/-! Free-ultrafilter evaluations on the actual quotient ℓ∞/c₀. They are
contractive, separate quotient classes, and localize strict real inequalities
on infinite subsets. No Stone--Čech identification is assumed. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon

def FreeNatUltrafilter := {U : Ultrafilter ℕ // (U : Filter ℕ) ≤ cofinite}

namespace FreeNatUltrafilter
instance : Coe FreeNatUltrafilter (Ultrafilter ℕ) := ⟨Subtype.val⟩
instance : Membership (Set ℕ) FreeNatUltrafilter := ⟨fun U A => A ∈ (U.val : Filter ℕ)⟩

theorem infinite_of_mem (U : FreeNatUltrafilter) {A : Set ℕ} (hA : A ∈ U) :
    A.Infinite := by
  intro hfin
  have hc : Aᶜ ∈ (U.val : Filter ℕ) := U.property hfin.compl_mem_cofinite
  exact Filter.nonempty_of_mem (Filter.inter_mem hA hc) |>.ne_empty (by simp)

theorem exists_mem {A : Set ℕ} (hA : A.Infinite) :
    ∃ U : FreeNatUltrafilter, A ∈ U := by
  letI : (cofinite ⊓ 𝓟 A).NeBot := cofinite_inf_principal_neBot_iff.mpr hA
  obtain ⟨U, hU⟩ := Filter.exists_ultrafilter_le (cofinite ⊓ 𝓟 A)
  exact ⟨⟨U, hU.trans inf_le_left⟩, Filter.le_principal_iff.mp (hU.trans inf_le_right)⟩

end FreeNatUltrafilter

variable {𝕜 : Type*} [RCLike 𝕜]

def infinityQuotientMk : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] InfinityCZeroQuotient 𝕜 :=
  quotientMkL (scalarCZeroSubmodule 𝕜)

def infinityQuotientEval (U : FreeNatUltrafilter) : InfinityCZeroQuotient 𝕜 →L[𝕜] 𝕜 :=
  quotientLiftL (scalarCZeroSubmodule 𝕜) (scalarUltralimit U.val) (by
    intro x hx
    exact scalarUltralimit_eq_of_tendsto U.val x (hx.mono_left U.property))

@[simp] theorem infinityQuotientEval_mk (U : FreeNatUltrafilter)
    (x : lp (fun _ : ℕ => 𝕜) ∞) :
    infinityQuotientEval (𝕜 := 𝕜) U (infinityQuotientMk (𝕜 := 𝕜) x) = scalarUltralimit U.val x := rfl

theorem norm_infinityQuotientEval_le (U : FreeNatUltrafilter) :
    ‖infinityQuotientEval (𝕜 := 𝕜) U‖ ≤ 1 :=
  (norm_quotientLiftL_le _ _ _).trans (norm_scalarUltralimit_le U.val)

theorem norm_infinityQuotientEval_apply_le (U : FreeNatUltrafilter)
    (x : InfinityCZeroQuotient 𝕜) : ‖infinityQuotientEval (𝕜 := 𝕜) U x‖ ≤ ‖x‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norm_infinityQuotientEval_le (𝕜 := 𝕜) U) (norm_nonneg x))

theorem infinityQuotient_eq_zero_of_eval_eq_zero (x : InfinityCZeroQuotient 𝕜)
    (hx : ∀ U : FreeNatUltrafilter, infinityQuotientEval (𝕜 := 𝕜) U x = 0) : x = 0 := by
  induction x using Quotient.inductionOn' with
  | h x =>
    apply (Submodule.Quotient.mk_eq_zero (scalarCZeroSubmodule 𝕜)).mpr
    apply (mem_filterNullSubmodule_iff cofinite x).mpr
    intro ε hε
    by_contra hsmall
    have hlarge : {n : ℕ | ε ≤ ‖x n‖}.Infinite := by
      simpa only [Filter.mem_cofinite, Set.compl_setOf, not_lt] using hsmall
    obtain ⟨U, hU⟩ := FreeNatUltrafilter.exists_mem hlarge
    have hlim := (scalarUltralimit_tendsto U.val x).norm
    have hle : ε ≤ ‖scalarUltralimit U.val x‖ := ge_of_tendsto hlim hU
    have hz : scalarUltralimit U.val x = 0 := hx U
    rw [hz, norm_zero] at hle
    exact (not_le_of_gt hε) hle

@[ext] theorem infinityQuotient_ext {x y : InfinityCZeroQuotient 𝕜}
    (h : ∀ U : FreeNatUltrafilter, infinityQuotientEval (𝕜 := 𝕜) U x = infinityQuotientEval (𝕜 := 𝕜) U y) :
    x = y := by
  apply sub_eq_zero.mp
  apply infinityQuotient_eq_zero_of_eval_eq_zero
  intro U
  simp only [map_sub, h U, sub_self]

theorem infinityQuotient_real_localize (x : InfinityCZeroQuotient ℝ)
    (U : FreeNatUltrafilter) {A : Set ℕ} (hA : A ∈ U) {a : ℝ}
    (ha : a < infinityQuotientEval (𝕜 := ℝ) U x) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧
      ∀ V : FreeNatUltrafilter, B ∈ V → a < infinityQuotientEval (𝕜 := ℝ) V x := by
  induction x using Quotient.inductionOn' with
  | h x =>
    obtain ⟨b, hab, hb⟩ := exists_between ha
    have hlim := scalarUltralimit_tendsto U.val x
    have hlevel : {n : ℕ | b < x n} ∈ (U.val : Filter ℕ) :=
      hlim.eventually (eventually_gt_nhds hb)
    let B : Set ℕ := A ∩ {n | b < x n}
    have hB : B ∈ U := Filter.inter_mem hA hlevel
    refine ⟨B, Set.inter_subset_left, U.infinite_of_mem hB, ?_⟩
    intro V hV
    apply hab.trans_le
    exact ge_of_tendsto (scalarUltralimit_tendsto V.val x)
      (Filter.mem_of_superset hV (fun n hn => (show b < x n from hn.2).le))

end ThesisCommon


