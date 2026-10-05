import ThesisCommon.Analysis.ScalarUltralimit
import ThesisCommon.Analysis.LpOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Coordinate ultralimits of uniformly bounded finite-p sequences remain in
the actual lp space, with no increase in norm. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 ι κ : Type*} [RCLike 𝕜]

def boundedLpCoordinate (p : BanachExponent) (k : κ) :
    lp (fun _ : ι => lp (fun _ : κ => 𝕜) p.val) ∞ →L[𝕜] lp (fun _ : ι => 𝕜) ∞ :=
  lpDiagonal ∞ (fun _ : ι => lpCoordinate (𝕜 := 𝕜) p.val k) 1 zero_le_one
    (fun _ => norm_lpCoordinate_le p.val k)

@[simp] theorem boundedLpCoordinate_apply (p : BanachExponent) (k : κ)
    (x : lp (fun _ : ι => lp (fun _ : κ => 𝕜) p.val) ∞) (i : ι) :
    boundedLpCoordinate p k x i = x i k := rfl

def lpUltralimitCoordinate (p : BanachExponent) (U : Ultrafilter ι) (k : κ) :
    lp (fun _ : ι => lp (fun _ : κ => 𝕜) p.val) ∞ →L[𝕜] 𝕜 :=
  (scalarUltralimit U).comp (boundedLpCoordinate p k)

theorem lpUltralimitCoordinate_tendsto (p : BanachExponent) (U : Ultrafilter ι)
    (x : lp (fun _ : ι => lp (fun _ : κ => 𝕜) p.val) ∞) (k : κ) :
    Tendsto (fun i => x i k) (U : Filter ι) (𝓝 (lpUltralimitCoordinate p U k x)) :=
  scalarUltralimit_tendsto U (boundedLpCoordinate p k x)

theorem sum_rpow_lpUltralimitCoordinate_le (p : BanachExponent) (hp : 0 < p.val.toReal)
    (U : Ultrafilter ι) (x : lp (fun _ : ι => lp (fun _ : κ => 𝕜) p.val) ∞) (s : Finset κ) :
    ∑ k ∈ s, ‖lpUltralimitCoordinate p U k x‖ ^ p.val.toReal ≤ ‖x‖ ^ p.val.toReal := by
  have hlim : Tendsto (fun i => ∑ k ∈ s, ‖x i k‖ ^ p.val.toReal) (U : Filter ι)
      (𝓝 (∑ k ∈ s, ‖lpUltralimitCoordinate p U k x‖ ^ p.val.toReal)) :=
    tendsto_finset_sum s (fun k _ => (lpUltralimitCoordinate_tendsto p U x k).norm.rpow_const
      (Or.inr hp.le))
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun i =>
    (lp.sum_rpow_le_norm_rpow hp (x i) s).trans
      (Real.rpow_le_rpow (norm_nonneg _) (lp.norm_apply_le_norm ENNReal.top_ne_zero x i) hp.le))

def lpCoordinateUltralimit (p : BanachExponent) (hp : 0 < p.val.toReal) (U : Ultrafilter ι) :
    lp (fun _ : ι => lp (fun _ : κ => 𝕜) p.val) ∞ →L[𝕜] lp (fun _ : κ => 𝕜) p.val :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun k => lpUltralimitCoordinate p U k x,
        memℓp_gen' (sum_rpow_lpUltralimitCoordinate_le p hp U x)⟩
      map_add' := fun x y => by
        apply lp.ext
        funext k
        exact map_add (lpUltralimitCoordinate p U k) x y
      map_smul' := fun c x => by
        apply lp.ext
        funext k
        exact map_smul (lpUltralimitCoordinate p U k) c x }
    1 (fun x => by
      simp only [one_mul]
      exact lp.norm_le_of_forall_sum_le hp (norm_nonneg x)
        (sum_rpow_lpUltralimitCoordinate_le p hp U x))

@[simp] theorem lpCoordinateUltralimit_apply (p : BanachExponent) (hp : 0 < p.val.toReal)
    (U : Ultrafilter ι) (x : lp (fun _ : ι => lp (fun _ : κ => 𝕜) p.val) ∞) (k : κ) :
    lpCoordinateUltralimit p hp U x k = lpUltralimitCoordinate p U k x := rfl

theorem norm_lpCoordinateUltralimit_le (p : BanachExponent) (hp : 0 < p.val.toReal)
    (U : Ultrafilter ι) :
    ‖lpCoordinateUltralimit (𝕜 := 𝕜) (κ := κ) p hp U‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem lpCoordinateUltralimit_eq_of_tendsto (p : BanachExponent) (hp : 0 < p.val.toReal)
    (U : Ultrafilter ι) (x : lp (fun _ : ι => lp (fun _ : κ => 𝕜) p.val) ∞)
    {y : lp (fun _ : κ => 𝕜) p.val} (hxy : ∀ k, Tendsto (fun i => x i k) U (𝓝 (y k))) :
    lpCoordinateUltralimit p hp U x = y := by
  apply lp.ext
  funext k
  exact tendsto_nhds_unique (lpUltralimitCoordinate_tendsto p U x k) (hxy k)

end ThesisCommon

