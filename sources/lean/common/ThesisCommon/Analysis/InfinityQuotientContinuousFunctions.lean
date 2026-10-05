import ThesisCommon.Analysis.FreeNatUltrafilterTopology
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Operator.Banach

/-! The scalar quotient is represented by genuine continuous functions on
the compact space of free ultrafilters. The proof uses compact scalar
ultralimits and real Tietze extension; it makes no vector-valued quotient
identification. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
variable {𝕜 : Type*} [RCLike 𝕜]

theorem continuous_scalarUltralimit (x : lp (fun _ : ℕ => 𝕜) ∞) :
    Continuous (fun U : Ultrafilter ℕ => scalarUltralimit U x) := by
  let K := Metric.closedBall (0 : 𝕜) ‖x‖
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : 𝕜) ‖x‖)
  let f : ℕ → K := fun n => ⟨x n, by
    change x n ∈ Metric.closedBall (0 : 𝕜) ‖x‖
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero x n⟩
  have he (U : Ultrafilter ℕ) : scalarUltralimit U x =
      (Ultrafilter.extend f U).val := by
    apply scalarUltralimit_eq_of_tendsto
    have h : Tendsto f (U : Filter ℕ) (𝓝 (Ultrafilter.extend f U)) :=
      ultrafilter_extend_eq_iff.mp rfl
    exact continuous_subtype_val.continuousAt.tendsto.comp h
  simp_rw [he]
  exact continuous_subtype_val.comp (continuous_ultrafilter_extend f)

theorem continuous_infinityQuotientEval (x : InfinityCZeroQuotient 𝕜) :
    Continuous (fun U : FreeNatUltrafilter => infinityQuotientEval (𝕜 := 𝕜) U x) := by
  induction x using Quotient.inductionOn' with
  | h x => exact (continuous_scalarUltralimit x).comp continuous_subtype_val

def infinityQuotientContinuous : InfinityCZeroQuotient 𝕜 →L[𝕜] C(FreeNatUltrafilter, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun U => infinityQuotientEval (𝕜 := 𝕜) U x,
        continuous_infinityQuotientEval x⟩
      map_add' := fun x y => by
        ext U
        exact (infinityQuotientEval (𝕜 := 𝕜) U).map_add x y
      map_smul' := fun c x => by
        ext U
        exact (infinityQuotientEval (𝕜 := 𝕜) U).map_smul c x }
    1 (fun x => by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
      exact fun U => by simpa only [one_mul] using
        norm_infinityQuotientEval_apply_le (𝕜 := 𝕜) U x)

@[simp] theorem infinityQuotientContinuous_apply (x : InfinityCZeroQuotient 𝕜)
    (U : FreeNatUltrafilter) : infinityQuotientContinuous (𝕜 := 𝕜) x U =
      infinityQuotientEval (𝕜 := 𝕜) U x := rfl

theorem norm_infinityQuotientContinuous_le : ‖infinityQuotientContinuous (𝕜 := 𝕜)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem infinityQuotientContinuous_injective :
    Function.Injective (infinityQuotientContinuous (𝕜 := 𝕜)) := by
  intro x y h
  apply infinityQuotient_ext
  exact fun U => congrArg (fun f : C(FreeNatUltrafilter, 𝕜) => f U) h

theorem freeNatUltrafilter_exists_scalar_extension (f : C(FreeNatUltrafilter, 𝕜)) :
    ∃ g : C(Ultrafilter ℕ, 𝕜), ∀ U : FreeNatUltrafilter, g U.val = f U := by
  let fr : C(FreeNatUltrafilter, ℝ) := ⟨fun U => RCLike.re (f U),
    RCLike.continuous_re.comp f.continuous⟩
  let fi : C(FreeNatUltrafilter, ℝ) := ⟨fun U => RCLike.im (f U),
    RCLike.continuous_im.comp f.continuous⟩
  obtain ⟨gr, hgr⟩ := fr.exists_restrict_eq FreeNatUltrafilter.isClosed_setOf_free
  obtain ⟨gi, hgi⟩ := fi.exists_restrict_eq FreeNatUltrafilter.isClosed_setOf_free
  refine ⟨⟨fun U => (gr U : 𝕜) + (gi U : 𝕜) * RCLike.I,
    (RCLike.continuous_ofReal.comp gr.continuous).add
      ((RCLike.continuous_ofReal.comp gi.continuous).mul continuous_const)⟩, ?_⟩
  intro U
  have hr := congrArg (fun h : C(FreeNatUltrafilter, ℝ) => h U) hgr
  have hi := congrArg (fun h : C(FreeNatUltrafilter, ℝ) => h U) hgi
  change (gr U.val : 𝕜) + (gi U.val : 𝕜) * RCLike.I = f U
  change gr U.val = RCLike.re (f U) at hr
  change gi U.val = RCLike.im (f U) at hi
  rw [hr, hi, RCLike.re_add_im]

theorem infinityQuotientContinuous_surjective :
    Function.Surjective (infinityQuotientContinuous (𝕜 := 𝕜)) := by
  intro f
  obtain ⟨g, hg⟩ := freeNatUltrafilter_exists_scalar_extension f
  let x : lp (fun _ : ℕ => 𝕜) ∞ := ⟨fun n => g (pure n),
    memℓp_infty_iff.mpr ⟨‖g‖, by
      rintro a ⟨n, rfl⟩
      exact g.norm_coe_le_norm (pure n)⟩⟩
  refine ⟨infinityQuotientMk (𝕜 := 𝕜) x, ?_⟩
  ext U
  change scalarUltralimit U.val x = f U
  rw [← hg U]
  exact scalarUltralimit_eq_of_tendsto _ x
    (g.continuous.continuousAt.tendsto.comp (Ultrafilter.tendsto_pure_self U.val))

def infinityQuotientContinuousEquiv :
    InfinityCZeroQuotient 𝕜 ≃L[𝕜] C(FreeNatUltrafilter, 𝕜) :=
  ContinuousLinearEquiv.ofBijective (infinityQuotientContinuous (𝕜 := 𝕜))
    (LinearMap.ker_eq_bot.mpr infinityQuotientContinuous_injective)
    (LinearMap.range_eq_top.mpr infinityQuotientContinuous_surjective)

@[simp] theorem infinityQuotientContinuousEquiv_apply (x : InfinityCZeroQuotient 𝕜)
    (U : FreeNatUltrafilter) : infinityQuotientContinuousEquiv (𝕜 := 𝕜) x U =
      infinityQuotientEval (𝕜 := 𝕜) U x := rfl

end ThesisCommon
