import CKEUPFP.OperatorFields
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Strongly continuous multipliers

This file proves Lemma `lem:multipliers` of the paper. Strong continuity is
continuity on each fixed vector; no continuity in operator norm is assumed.
-/

noncomputable section

universe u v w

namespace CKEUPFP

open Filter
open scoped Topology

variable {𝕜 : Type u} [RCLike 𝕜]
variable {K : Type v} [TopologicalSpace K]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Applying a uniformly bounded, strongly continuous field to a continuous
vector-valued function is continuous. -/
theorem continuous_strong_apply (A : K → E →L[𝕜] E)
    (hA : IsStronglyContinuous A) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ t, ‖A t‖ ≤ M) (f : K → E) (hf : Continuous f) :
    Continuous (fun t => A t (f t)) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hden : 0 < 2 * (M + 1) := by positivity
  have hsmall : 0 < ε / (2 * (M + 1)) := div_pos hε hden
  have h₁ := (Metric.continuousAt_iff'.mp (hf.continuousAt (x := t₀)))
    (ε / (2 * (M + 1))) hsmall
  have h₂ := (Metric.continuousAt_iff'.mp ((hA (f t₀)).continuousAt (x := t₀)))
    (ε / 2) (by positivity)
  filter_upwards [h₁, h₂] with t ht₁ ht₂
  have hdist : 0 ≤ dist (f t) (f t₀) := dist_nonneg
  have hterm : ‖A t‖ * dist (f t) (f t₀) < ε / 2 := by
    have hmul := (lt_div_iff₀ hden).mp ht₁
    have hop := hbound t
    nlinarith
  calc
    dist (A t (f t)) (A t₀ (f t₀)) ≤
        dist (A t (f t)) (A t (f t₀)) +
          dist (A t (f t₀)) (A t₀ (f t₀)) := dist_triangle _ _ _
    _ ≤ ‖A t‖ * dist (f t) (f t₀) +
          dist (A t (f t₀)) (A t₀ (f t₀)) := by
      gcongr
      exact (A t).dist_le_opNorm _ _
    _ < ε := by linarith

variable [CompactSpace K]

/-- The bounded multiplier induced by a strongly continuous field with an
explicit uniform bound. -/
def multiplier (A : K → E →L[𝕜] E) (hA : IsStronglyContinuous A)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ t, ‖A t‖ ≤ M) :
    C(K, E) →L[𝕜] C(K, E) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun t => A t (f t),
        continuous_strong_apply A hA hM hbound f f.continuous⟩
      map_add' := by
        intro f g
        ext t
        exact (A t).map_add (f t) (g t)
      map_smul' := by
        intro c f
        ext t
        exact (A t).map_smul c (f t) }
    M (by
      intro f
      apply (ContinuousMap.norm_le _ (mul_nonneg hM (norm_nonneg f))).mpr
      intro t
      calc
        ‖A t (f t)‖ ≤ ‖A t‖ * ‖f t‖ := (A t).le_opNorm _
        _ ≤ M * ‖f‖ := mul_le_mul (hbound t) (f.norm_coe_le_norm t)
          (norm_nonneg _) hM)

@[simp]
theorem multiplier_apply (A : K → E →L[𝕜] E) (hA : IsStronglyContinuous A)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ t, ‖A t‖ ≤ M)
    (f : C(K, E)) (t : K) :
    multiplier A hA M hM hbound f t = A t (f t) := rfl

theorem multiplier_norm_le (A : K → E →L[𝕜] E) (hA : IsStronglyContinuous A)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ t, ‖A t‖ ≤ M) :
    ‖multiplier A hA M hM hbound‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hM (norm_nonneg f))).mpr
  intro t
  simp only [multiplier_apply]
  exact ((A t).le_opNorm _).trans
    (mul_le_mul (hbound t) (f.norm_coe_le_norm t) (norm_nonneg _) hM)

/-- Constant functions certify the reverse norm inequality, including when
the domain is empty (there are then no points to test). -/
theorem field_norm_le_multiplier_norm (A : K → E →L[𝕜] E)
    (hA : IsStronglyContinuous A) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t, ‖A t‖ ≤ M) (t : K) :
    ‖A t‖ ≤ ‖multiplier A hA M hM hbound‖ := by
  apply (A t).opNorm_le_bound (norm_nonneg _)
  intro x
  have hconst : ‖ContinuousMap.const K x‖ ≤ ‖x‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
    intro s
    exact le_rfl
  calc
    ‖A t x‖ = ‖multiplier A hA M hM hbound (ContinuousMap.const K x) t‖ := rfl
    _ ≤ ‖multiplier A hA M hM hbound (ContinuousMap.const K x)‖ :=
      ContinuousMap.norm_coe_le_norm _ t
    _ ≤ ‖multiplier A hA M hM hbound‖ * ‖ContinuousMap.const K x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖multiplier A hA M hM hbound‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left hconst (norm_nonneg _)

/-- Exact operator norm in Lemma `lem:multipliers`. The formula also holds
for the empty compact space, where the real supremum of the empty set is zero. -/
theorem multiplier_norm (A : K → E →L[𝕜] E)
    (hA : IsStronglyContinuous A) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t, ‖A t‖ ≤ M) :
    ‖multiplier A hA M hM hbound‖ = sSup (Set.range fun t => ‖A t‖) := by
  have hbounded : BddAbove (Set.range fun t => ‖A t‖) := by
    refine ⟨M, ?_⟩
    rintro r ⟨t, rfl⟩
    exact hbound t
  have hnonneg : 0 ≤ sSup (Set.range fun t => ‖A t‖) := by
    apply Real.sSup_nonneg
    rintro r ⟨t, rfl⟩
    exact norm_nonneg _
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ hnonneg
    intro f
    apply (ContinuousMap.norm_le _ (mul_nonneg hnonneg (norm_nonneg f))).mpr
    intro t
    simp only [multiplier_apply]
    exact ((A t).le_opNorm _).trans
      (mul_le_mul (le_csSup hbounded (Set.mem_range_self t))
        (f.norm_coe_le_norm t) (norm_nonneg _) hnonneg)
  · apply Real.sSup_le _ (norm_nonneg _)
    rintro r ⟨t, rfl⟩
    exact field_norm_le_multiplier_norm A hA M hM hbound t

/-- The full existence and norm assertion of Lemma `lem:multipliers`, with
the uniform bound expressed in the paper's vocabulary. -/
theorem exists_multiplier (A : K → E →L[𝕜] E)
    (hA : IsStronglyContinuous A) (hbounded : IsUniformlyBounded A) :
    ∃ M : C(K, E) →L[𝕜] C(K, E),
      (∀ f t, M f t = A t (f t)) ∧
        ‖M‖ = sSup (Set.range fun t => ‖A t‖) := by
  obtain ⟨B, hB, hbound⟩ := hbounded
  exact ⟨multiplier A hA B hB hbound, fun _ _ => rfl,
    multiplier_norm A hA B hB hbound⟩

/-- The multiplier is independent of the choice of a uniform bound. -/
theorem multiplier_eq (A : K → E →L[𝕜] E)
    (hA : IsStronglyContinuous A) (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundM : ∀ t, ‖A t‖ ≤ M) (hboundN : ∀ t, ‖A t‖ ≤ N) :
    multiplier A hA M hM hboundM = multiplier A hA N hN hboundN := by
  ext f t
  rfl

/-- Pointwise factorisation by three operator fields gives precisely the
factorisation by their multipliers used in Section 4. -/
theorem multiplier_factorization
    (L A R : K → E →L[𝕜] E)
    (hL : IsStronglyContinuous L) (hA : IsStronglyContinuous A)
    (hR : IsStronglyContinuous R)
    (ML MA MR : ℝ) (hML : 0 ≤ ML) (hMA : 0 ≤ MA) (hMR : 0 ≤ MR)
    (hboundL : ∀ t, ‖L t‖ ≤ ML) (hboundA : ∀ t, ‖A t‖ ≤ MA)
    (hboundR : ∀ t, ‖R t‖ ≤ MR)
    (hfactor : ∀ t, ((L t).comp (A t)).comp (R t) =
      ContinuousLinearMap.id 𝕜 E) :
    ((multiplier L hL ML hML hboundL).comp
      (multiplier A hA MA hMA hboundA)).comp
      (multiplier R hR MR hMR hboundR) =
        ContinuousLinearMap.id 𝕜 C(K, E) := by
  ext f t
  have ht := congrArg (fun S : E →L[𝕜] E => S (f t)) (hfactor t)
  simpa only [ContinuousLinearMap.comp_apply, multiplier_apply,
    ContinuousLinearMap.id_apply] using ht

end CKEUPFP
