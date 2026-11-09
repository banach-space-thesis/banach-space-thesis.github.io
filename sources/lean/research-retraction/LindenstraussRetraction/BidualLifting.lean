import LindenstraussRetraction.SummationQuotient
import LindenstraussRetraction.BidualMap
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Compactness.Compact

/-!
# Isometric lifting of the summation quotient into its bidual

A fixed ultrafilter extending the tails of the natural numbers gives scalar
limits of the bounded sequences `f (T_m x)`. These limits define continuous
bidual functionals. Linearity follows from uniqueness of scalar limits, and
norm convergence of `Q T_m x` gives `Q** S x = J x`.
-/

noncomputable section

open Filter Topology

namespace LindenstraussRetraction

universe u v w

set_option synthInstance.maxSize 512

private def liftingUltrafilter : Ultrafilter ℕ := Ultrafilter.of atTop

private theorem liftingUltrafilter_le_atTop :
    (liftingUltrafilter : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop

variable {𝕜 : Type w} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem bounded_scalar_tendsto_limUnder
    (a : ℕ → 𝕜) (C : ℝ) (ha : ∀ n, ‖a n‖ ≤ C) :
    Tendsto a (liftingUltrafilter : Filter ℕ)
      (𝓝 (limUnder (liftingUltrafilter : Filter ℕ) a)) := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  have hm : Metric.closedBall (0 : 𝕜) C ∈ liftingUltrafilter.map a := by
    change ∀ᶠ n in (liftingUltrafilter : Filter ℕ),
      a n ∈ Metric.closedBall (0 : 𝕜) C
    exact Eventually.of_forall (fun n => by simpa [Metric.mem_closedBall] using ha n)
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : 𝕜) C).ultrafilter_le_nhds'
    (liftingUltrafilter.map a) hm
  exact tendsto_nhds_limUnder ⟨z, hz⟩

/-- Scalar evaluation of the weak-star limit of a contractive approximation. -/
def approximationBidualEvaluation (T : ℕ → F →L[𝕜] E) (x : F)
    (f : StrongDual 𝕜 E) : 𝕜 :=
  limUnder (liftingUltrafilter : Filter ℕ) (fun n => f (T n x))

theorem approximationBidualEvaluation_tendsto
    (T : ℕ → F →L[𝕜] E) (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖)
    (x : F) (f : StrongDual 𝕜 E) :
    Tendsto (fun n => f (T n x)) (liftingUltrafilter : Filter ℕ)
      (𝓝 (approximationBidualEvaluation T x f)) := by
  apply bounded_scalar_tendsto_limUnder _ (‖f‖ * ‖x‖)
  intro n
  exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hT n x) (norm_nonneg f))

theorem norm_approximationBidualEvaluation_le
    (T : ℕ → F →L[𝕜] E) (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖)
    (x : F) (f : StrongDual 𝕜 E) :
    ‖approximationBidualEvaluation T x f‖ ≤ ‖f‖ * ‖x‖ := by
  apply le_of_tendsto (approximationBidualEvaluation_tendsto T hT x f).norm
  exact Eventually.of_forall (fun n =>
    (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hT n x) (norm_nonneg f)))

/-- Each weak-star limit is a continuous functional on the continuous dual. -/
def approximationBidualPoint (T : ℕ → F →L[𝕜] E)
    (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) (x : F) : Bidual 𝕜 E :=
  ({ toFun := approximationBidualEvaluation T x
     map_add' f g := by
       apply tendsto_nhds_unique (approximationBidualEvaluation_tendsto T hT x (f + g))
       simpa only [ContinuousLinearMap.add_apply] using
         (approximationBidualEvaluation_tendsto T hT x f).add
           (approximationBidualEvaluation_tendsto T hT x g)
     map_smul' c f := by
       apply tendsto_nhds_unique (approximationBidualEvaluation_tendsto T hT x (c • f))
       simpa only [ContinuousLinearMap.smul_apply] using
         (approximationBidualEvaluation_tendsto T hT x f).const_smul c
     } : StrongDual 𝕜 E →ₗ[𝕜] 𝕜).mkContinuous ‖x‖ (fun f => by
       simpa only [mul_comm] using norm_approximationBidualEvaluation_le T hT x f)

@[simp] theorem approximationBidualPoint_apply
    (T : ℕ → F →L[𝕜] E) (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖)
    (x : F) (f : StrongDual 𝕜 E) :
    approximationBidualPoint T hT x f = approximationBidualEvaluation T x f := rfl

theorem norm_approximationBidualPoint_le
    (T : ℕ → F →L[𝕜] E) (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) (x : F) :
    ‖approximationBidualPoint T hT x‖ ≤ ‖x‖ := by
  apply (approximationBidualPoint T hT x).opNorm_le_bound (norm_nonneg x)
  intro f
  simpa only [approximationBidualPoint_apply, mul_comm] using
    norm_approximationBidualEvaluation_le T hT x f

/-- Contractive linear approximations define a contractive linear bidual map. -/
def approximationBidualLift (T : ℕ → F →L[𝕜] E)
    (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) : F →L[𝕜] Bidual 𝕜 E := by
  let L : F →ₗ[𝕜] Bidual 𝕜 E :=
    { toFun := approximationBidualPoint T hT
      map_add' x y := by
        ext f
        apply tendsto_nhds_unique (approximationBidualEvaluation_tendsto T hT (x + y) f)
        simpa only [map_add] using
          (approximationBidualEvaluation_tendsto T hT x f).add
            (approximationBidualEvaluation_tendsto T hT y f)
      map_smul' c x := by
        ext f
        apply tendsto_nhds_unique (approximationBidualEvaluation_tendsto T hT (c • x) f)
        simpa only [map_smul] using
          (approximationBidualEvaluation_tendsto T hT x f).const_smul c }
  exact L.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜) (E := F) (F := Bidual 𝕜 E)
    (σ := RingHom.id 𝕜) 1 (fun x => by
    change ‖approximationBidualPoint T hT x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using norm_approximationBidualPoint_le T hT x)

@[simp] theorem approximationBidualLift_apply
    (T : ℕ → F →L[𝕜] E) (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) (x : F) :
    approximationBidualLift T hT x = approximationBidualPoint T hT x := rfl

theorem approximationBidualLift_rightInverse
    (T : ℕ → F →L[𝕜] E) (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖)
    (q : E →L[𝕜] F)
    (happrox : ∀ x, Tendsto (fun n => q (T n x)) atTop (𝓝 x)) (x : F) :
    bidualMap q (approximationBidualLift T hT x) = bidualEmbedding 𝕜 F x := by
  ext f
  apply tendsto_nhds_unique (approximationBidualEvaluation_tendsto T hT x (transpose q f))
  exact ((f.continuous.tendsto x).comp (happrox x)).mono_left liftingUltrafilter_le_atTop

theorem approximationBidualLift_norm_eq
    (T : ℕ → F →L[𝕜] E) (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖)
    (q : E →L[𝕜] F) (hq : ‖q‖ ≤ 1)
    (happrox : ∀ x, Tendsto (fun n => q (T n x)) atTop (𝓝 x)) (x : F) :
    ‖approximationBidualLift T hT x‖ = ‖x‖ := by
  apply le_antisymm (norm_approximationBidualPoint_le T hT x)
  calc
    ‖x‖ = ‖bidualEmbedding 𝕜 F x‖ := (bidualEmbedding 𝕜 F).norm_map x |>.symm
    _ = ‖bidualMap q (approximationBidualLift T hT x)‖ := by
      rw [approximationBidualLift_rightInverse T hT q happrox]
    _ ≤ ‖q‖ * ‖approximationBidualLift T hT x‖ := norm_bidualMap_apply_le _ _
    _ ≤ 1 * ‖approximationBidualLift T hT x‖ :=
      mul_le_mul_of_nonneg_right hq (approximationBidualLift T hT x).opNorm_nonneg
    _ = ‖approximationBidualLift T hT x‖ := one_mul _

section Summation

variable (𝕜)

/-- The concrete `S : c₀ → Y**` from `prop:quotient-lifting`. -/
def summationBidualLift : C0 𝕜 →L[𝕜] Bidual 𝕜 (SummationSpace 𝕜) :=
  approximationBidualLift (summationApproximateLift 𝕜)
    (norm_summationApproximateLift_le 𝕜)

private theorem summationApproximateLift_tendsto (x : C0 𝕜) :
    Tendsto (fun n => summationOperator 𝕜 (summationApproximateLift 𝕜 n x))
      atTop (𝓝 x) := by
  simpa only [summationOperator_approximateLift] using
    (c0Truncation_tendsto 𝕜 x).comp (tendsto_add_atTop_nat 1)

@[simp] theorem summationBidualLift_rightInverse (x : C0 𝕜) :
    bidualMap (summationOperator 𝕜) (summationBidualLift 𝕜 x) =
      bidualEmbedding 𝕜 (C0 𝕜) x :=
  approximationBidualLift_rightInverse _ _ _ (summationApproximateLift_tendsto 𝕜) x

@[simp] theorem norm_summationBidualLift (x : C0 𝕜) :
    ‖summationBidualLift 𝕜 x‖ = ‖x‖ :=
  approximationBidualLift_norm_eq _ _ _ (norm_summationOperator_le 𝕜)
    (summationApproximateLift_tendsto 𝕜) x

/-- The concrete lifting bundled as a linear isometry. -/
def summationBidualLifting : C0 𝕜 →ₗᵢ[𝕜] Bidual 𝕜 (SummationSpace 𝕜) :=
  { summationBidualLift 𝕜 with norm_map' := norm_summationBidualLift 𝕜 }

theorem summationBidualLift_isometry : Isometry (summationBidualLift 𝕜) :=
  (summationBidualLifting 𝕜).isometry

theorem summationBidualLift_comp :
    (bidualMap (summationOperator 𝕜)).comp (summationBidualLift 𝕜) =
      (bidualEmbedding 𝕜 (C0 𝕜)).toContinuousLinearMap := by
  ext x f
  exact congrArg (fun z : Bidual 𝕜 (C0 𝕜) => z f)
    (summationBidualLift_rightInverse 𝕜 x)

end Summation

end LindenstraussRetraction
