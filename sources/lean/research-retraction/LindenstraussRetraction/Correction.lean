import LindenstraussRetraction.Statements
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Iterative correction of an approximate section

The geometric correction argument from Section 2 of the supplied paper.
The ball version below isolates the argument after homogeneous extension
of the sphere map. No quotient-map assumption is needed at this stage.
-/

noncomputable section

open scoped BigOperators
open Filter Topology

namespace LindenstraussRetraction

universe u v w

/-- A uniform limit of uniformly continuous maps is uniformly continuous. -/
theorem uniformContinuous_of_uniformLimit
    {A : Type u} {B : Type v} [PseudoMetricSpace A] [PseudoMetricSpace B]
    {F : ℕ → A → B} {f : A → B}
    (hF : ∀ n, UniformContinuous (F n)) (hf : TendstoUniformly F f atTop) :
    UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformly_iff.1 hf) (ε / 3) (by positivity))
  obtain ⟨δ, hδ, hδF⟩ := (Metric.uniformContinuous_iff.1 (hF N)) (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  have hx := hN N (le_refl _) x
  have hy := hN N (le_refl _) y
  have hmid := hδF hxy
  calc
    dist (f x) (f y) ≤ dist (f x) (F N x) + dist (F N x) (F N y) +
        dist (F N y) (f y) := dist_triangle4 _ _ _ _
    _ < ε := by rw [dist_comm] at hy; linarith

variable {𝕜 : Type w} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The iterative correction step for a uniformly continuous approximate
section on the ball with norm-proportional bounds. -/
theorem hasUniformSectionOnUnitBall_of_ballApproximation
    [CompleteSpace E]
    (q : E →L[𝕜] W) (Φ : UnitBall W → E) (hΦ : UniformContinuous Φ)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (ha1 : a < 1)
    (hbound : ∀ x, ‖Φ x‖ ≤ C * ‖x.val‖)
    (herror : ∀ x, ‖x.val - q (Φ x)‖ ≤ a * ‖x.val‖) :
    HasUniformSectionOnUnitBall q := by
  classical
  let g : UnitBall W → UnitBall W := fun x =>
    ⟨x.val - q (Φ x), (herror x).trans (by nlinarith [x.property, norm_nonneg x.val])⟩
  have hg : UniformContinuous g :=
    (uniformContinuous_subtype_val.sub (q.uniformContinuous.comp hΦ)).subtype_mk _
  have hg_norm (x : UnitBall W) (n : ℕ) : ‖(g^[n] x).val‖ ≤ a ^ n * ‖x.val‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖(g (g^[n] x)).val‖ ≤ a * ‖(g^[n] x).val‖ := herror _
        _ ≤ a * (a ^ n * ‖x.val‖) := mul_le_mul_of_nonneg_left ih ha
        _ = a ^ (n + 1) * ‖x.val‖ := by rw [pow_succ]; ring
  have hg_uc (n : ℕ) : UniformContinuous (g^[n]) := by
    induction n with
    | zero => exact uniformContinuous_id
    | succ n ih => simpa only [Function.iterate_succ] using ih.comp hg
  let f : ℕ → UnitBall W → E := fun n x => Φ (g^[n] x)
  have hf_bound (n : ℕ) (x : UnitBall W) : ‖f n x‖ ≤ C * a ^ n := by
    calc
      ‖f n x‖ ≤ C * ‖(g^[n] x).val‖ := hbound _
      _ ≤ C * (a ^ n * ‖x.val‖) := mul_le_mul_of_nonneg_left (hg_norm x n) hC
      _ ≤ C * (a ^ n * 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left x.property (pow_nonneg ha _)) hC
      _ = C * a ^ n := by ring
  have hsum : Summable (fun n : ℕ => C * a ^ n) :=
    (summable_geometric_of_lt_one ha ha1).mul_left C
  let s : UnitBall W → E := fun x => ∑' n, f n x
  have hs_uc : UniformContinuous s := by
    apply uniformContinuous_of_uniformLimit
      (F := fun N x => ∑ n ∈ Finset.range N, f n x)
    · intro N
      induction N with
      | zero => simpa using (uniformContinuous_const : UniformContinuous (fun _ : UnitBall W => (0 : E)))
      | succ N ih =>
        simpa only [Finset.sum_range_succ] using ih.add (hΦ.comp (hg_uc N))
    · exact tendstoUniformly_tsum_nat hsum hf_bound
  refine ⟨s, hs_uc, fun x => ?_⟩
  have hf_sum : Summable (fun n => f n x) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hf_bound n x) hsum).of_norm
  have htel (N : ℕ) : q (∑ n ∈ Finset.range N, f n x) = x.val - (g^[N] x).val := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, map_add, ih, Function.iterate_succ_apply']
      change x.val - (g^[N] x).val + q (Φ (g^[N] x)) =
        x.val - ((g^[N] x).val - q (Φ (g^[N] x)))
      abel
  have hzero : Tendsto (fun N : ℕ => (g^[N] x).val) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (hg_norm x)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1).mul_const ‖x.val‖)
  have hleft : Tendsto (fun N : ℕ => q (∑ n ∈ Finset.range N, f n x)) atTop (𝓝 (q (s x))) :=
    q.continuous.tendsto _ |>.comp hf_sum.hasSum.tendsto_sum_nat
  have hright : Tendsto (fun N : ℕ => x.val - (g^[N] x).val) atTop (𝓝 x.val) := by
    simpa using tendsto_const_nhds.sub hzero
  exact tendsto_nhds_unique hleft (by simpa only [htel] using hright)

/-- A nonzero vector normalized to the unit sphere. -/
def normalizedUnitSphere (x : W) (hx : x ≠ 0) : UnitSphere W :=
  ⟨(‖x‖⁻¹ : 𝕜) • x, norm_smul_inv_norm hx⟩

theorem normalizedUnitSphere_recover (x : W) (hx : x ≠ 0) :
    (‖x‖ : 𝕜) • (normalizedUnitSphere (𝕜 := 𝕜) x hx).val = x := by
  simp only [normalizedUnitSphere, smul_smul]
  rw [mul_inv_cancel₀, one_smul]
  apply norm_ne_zero_iff.1
  rw [RCLike.norm_coe_norm]
  exact norm_ne_zero_iff.2 hx

/-- Normalization has a uniform distance bound away from the origin. -/
theorem normalizedUnitSphere_dist_le (x y : W) (hx : x ≠ 0) (hy : y ≠ 0) :
    dist (normalizedUnitSphere (𝕜 := 𝕜) x hx)
      (normalizedUnitSphere (𝕜 := 𝕜) y hy) ≤ 2 * ‖x - y‖ / ‖x‖ := by
  let u := normalizedUnitSphere (𝕜 := 𝕜) x hx
  let v := normalizedUnitSphere (𝕜 := 𝕜) y hy
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have heq : (‖x‖ : 𝕜) • (u.val - v.val) =
      x - y + ((‖y‖ - ‖x‖ : ℝ) : 𝕜) • v.val := by
    rw [RCLike.ofReal_sub, sub_smul, smul_sub,
      normalizedUnitSphere_recover, normalizedUnitSphere_recover]
    abel
  have hmul : ‖x‖ * ‖u.val - v.val‖ ≤ 2 * ‖x - y‖ := by
    calc
      ‖x‖ * ‖u.val - v.val‖ = ‖(‖x‖ : 𝕜) • (u.val - v.val)‖ := by simp [norm_smul]
      _ = ‖x - y + ((‖y‖ - ‖x‖ : ℝ) : 𝕜) • v.val‖ := congrArg norm heq
      _ ≤ ‖x - y‖ + ‖((‖y‖ - ‖x‖ : ℝ) : 𝕜) • v.val‖ := norm_add_le _ _
      _ = ‖x - y‖ + |‖y‖ - ‖x‖| := by rw [norm_smul, RCLike.norm_ofReal, v.property, mul_one]
      _ ≤ 2 * ‖x - y‖ := by
        have h := abs_norm_sub_norm_le y x
        rw [norm_sub_rev] at h
        linarith
  rw [Subtype.dist_eq, dist_eq_norm]
  apply (le_div_iff₀ hr).2
  nlinarith

/-- Positive homogeneous extension of a sphere map, including its value at zero. -/
def sphereHomogeneousExtension (φ : UnitSphere W → E) (x : W) : E := by
  classical
  exact if hx : x = 0 then 0 else
    (‖x‖ : 𝕜) • φ (normalizedUnitSphere (𝕜 := 𝕜) x hx)

theorem sphereHomogeneousExtension_norm_le (φ : UnitSphere W → E)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) (x : W) :
    ‖sphereHomogeneousExtension (𝕜 := 𝕜) φ x‖ ≤ C * ‖x‖ := by
  by_cases hx : x = 0
  · simp [sphereHomogeneousExtension, hx]
  · rw [sphereHomogeneousExtension, dif_neg hx, norm_smul, RCLike.norm_coe_norm]
    nlinarith [hbound (normalizedUnitSphere (𝕜 := 𝕜) x hx), norm_nonneg x]

theorem sphereHomogeneousExtension_sub_le (φ : UnitSphere W → E)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖φ x‖ ≤ C)
    (x y : UnitBall W) (hx : x.val ≠ 0) (hy : y.val ≠ 0) :
    ‖sphereHomogeneousExtension (𝕜 := 𝕜) φ x.val -
      sphereHomogeneousExtension (𝕜 := 𝕜) φ y.val‖ ≤
      ‖φ (normalizedUnitSphere (𝕜 := 𝕜) x.val hx) -
        φ (normalizedUnitSphere (𝕜 := 𝕜) y.val hy)‖ + C * ‖x.val - y.val‖ := by
  let u := normalizedUnitSphere (𝕜 := 𝕜) x.val hx
  let v := normalizedUnitSphere (𝕜 := 𝕜) y.val hy
  have heq : (‖x.val‖ : 𝕜) • φ u - (‖y.val‖ : 𝕜) • φ v =
      (‖x.val‖ : 𝕜) • (φ u - φ v) + ((‖x.val‖ - ‖y.val‖ : ℝ) : 𝕜) • φ v := by
    rw [RCLike.ofReal_sub, sub_smul, smul_sub]
    abel
  rw [sphereHomogeneousExtension, dif_neg hx, sphereHomogeneousExtension, dif_neg hy]
  calc
    ‖(‖x.val‖ : 𝕜) • φ u - (‖y.val‖ : 𝕜) • φ v‖ =
        ‖(‖x.val‖ : 𝕜) • (φ u - φ v) + ((‖x.val‖ - ‖y.val‖ : ℝ) : 𝕜) • φ v‖ := congrArg norm heq
    _ ≤ ‖(‖x.val‖ : 𝕜) • (φ u - φ v)‖ +
        ‖((‖x.val‖ - ‖y.val‖ : ℝ) : 𝕜) • φ v‖ := norm_add_le _ _
    _ = ‖x.val‖ * ‖φ u - φ v‖ + |‖x.val‖ - ‖y.val‖| * ‖φ v‖ := by
      rw [norm_smul, norm_smul, RCLike.norm_coe_norm, RCLike.norm_ofReal]
    _ ≤ ‖φ u - φ v‖ + C * ‖x.val - y.val‖ := by
      have h1 := mul_le_mul_of_nonneg_right x.property (norm_nonneg (φ u - φ v))
      have h2 := mul_le_mul_of_nonneg_left (hbound v) (abs_nonneg (‖x.val‖ - ‖y.val‖))
      have h3 := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x.val y.val) hC
      nlinarith

/-- Bounded uniform continuity on the sphere gives uniform continuity of the
homogeneous extension on the closed unit ball, including at the origin. -/
theorem sphereHomogeneousExtension_uniformContinuous
    (φ : UnitSphere W → E) (hφ : UniformContinuous φ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖φ x‖ ≤ C) :
    UniformContinuous (fun x : UnitBall W => sphereHomogeneousExtension (𝕜 := 𝕜) φ x.val) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨η, hη, hηφ⟩ := (Metric.uniformContinuous_iff.1 hφ) (ε / 2) (by positivity)
  let t : ℝ := ε / (8 * (C + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hteq : 8 * (C + 1) * t = ε := by
    dsimp [t]
    field_simp
  have hCt : C * t < ε / 8 := by nlinarith
  refine ⟨min t (t * η / 4), by positivity, ?_⟩
  intro x y hxy
  have hd : ‖x.val - y.val‖ < min t (t * η / 4) := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hxy
  have hdt : ‖x.val - y.val‖ < t := hd.trans_le (min_le_left _ _)
  have hdη : ‖x.val - y.val‖ < t * η / 4 := hd.trans_le (min_le_right _ _)
  rw [dist_eq_norm]
  by_cases hxsmall : ‖x.val‖ < t
  · have hybound := norm_sub_norm_le y.val x.val
    rw [norm_sub_rev] at hybound
    have hy_small : ‖y.val‖ < 2 * t := by linarith
    calc
      ‖sphereHomogeneousExtension (𝕜 := 𝕜) φ x.val -
          sphereHomogeneousExtension (𝕜 := 𝕜) φ y.val‖ ≤
        ‖sphereHomogeneousExtension (𝕜 := 𝕜) φ x.val‖ +
          ‖sphereHomogeneousExtension (𝕜 := 𝕜) φ y.val‖ := norm_sub_le _ _
      _ ≤ C * ‖x.val‖ + C * ‖y.val‖ := add_le_add
        (sphereHomogeneousExtension_norm_le φ hbound _)
        (sphereHomogeneousExtension_norm_le φ hbound _)
      _ < ε := by nlinarith
  · have hr : t ≤ ‖x.val‖ := le_of_not_gt hxsmall
    have hx : x.val ≠ 0 := norm_pos_iff.1 (ht.trans_le hr)
    have hy : y.val ≠ 0 := by
      intro hyzero
      have hd' : ‖x.val‖ < t := by simpa [hyzero] using hdt
      linarith
    have hnormalized : dist (normalizedUnitSphere (𝕜 := 𝕜) x.val hx)
        (normalizedUnitSphere (𝕜 := 𝕜) y.val hy) < η := by
      apply (normalizedUnitSphere_dist_le x.val y.val hx hy).trans_lt
      apply (div_lt_iff₀ (ht.trans_le hr)).2
      nlinarith
    have hφdist := hηφ hnormalized
    rw [dist_eq_norm] at hφdist
    calc
      ‖sphereHomogeneousExtension (𝕜 := 𝕜) φ x.val -
          sphereHomogeneousExtension (𝕜 := 𝕜) φ y.val‖ ≤
        ‖φ (normalizedUnitSphere (𝕜 := 𝕜) x.val hx) -
          φ (normalizedUnitSphere (𝕜 := 𝕜) y.val hy)‖ + C * ‖x.val - y.val‖ :=
        sphereHomogeneousExtension_sub_le φ hC hbound x y hx hy
      _ < ε := by nlinarith

/-- The sphere approximation error scales proportionally to the norm in the
homogeneous extension. -/
theorem sphereHomogeneousExtension_error_le
    (q : E →L[𝕜] W) (φ : UnitSphere W → E)
    {a : ℝ} (herror : ∀ x : UnitSphere W, ‖q (φ x) - x.val‖ ≤ a) (x : W) :
    ‖x - q (sphereHomogeneousExtension (𝕜 := 𝕜) φ x)‖ ≤ a * ‖x‖ := by
  by_cases hx : x = 0
  · simp [sphereHomogeneousExtension, hx]
  · let u := normalizedUnitSphere (𝕜 := 𝕜) x hx
    rw [sphereHomogeneousExtension, dif_neg hx, map_smul]
    calc
      ‖x - (‖x‖ : 𝕜) • q (φ u)‖ = ‖(‖x‖ : 𝕜) • (u.val - q (φ u))‖ := by
        rw [smul_sub, normalizedUnitSphere_recover]
      _ = ‖x‖ * ‖u.val - q (φ u)‖ := by simp [norm_smul]
      _ ≤ a * ‖x‖ := by
        have h := herror u
        rw [norm_sub_rev] at h
        nlinarith [norm_nonneg x]

/-- Section 2, Lemma `lem:correction`, proved over both real and complex
scalars. The stronger proof does not use the quotient-map hypothesis. -/
theorem correction [CompleteSpace E] [CompleteSpace W] : CorrectionStatement (𝕜 := 𝕜) E W := by
  intro q _hq φ hφ hbounded a ha ha1 herror
  obtain ⟨C, hC, hbound⟩ := hbounded
  exact hasUniformSectionOnUnitBall_of_ballApproximation q
    (fun x => sphereHomogeneousExtension (𝕜 := 𝕜) φ x.val)
    (sphereHomogeneousExtension_uniformContinuous φ hφ hC hbound) hC ha ha1
    (fun x => sphereHomogeneousExtension_norm_le φ hbound x.val)
    (fun x => sphereHomogeneousExtension_error_le q φ herror x.val)

include 𝕜 in
omit [NormedSpace 𝕜 E] in
/-- A uniformly continuous map on a normed-space unit ball has bounded image.
The proof divides each radial segment into a fixed finite number of steps. -/
theorem uniformContinuous_unitBall_norm_bounded
    (f : UnitBall W → E) (hf : UniformContinuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨δ, hδ, hfδ⟩ := (Metric.uniformContinuous_iff.1 hf) 1 zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let N : ℕ := n + 1
  have hN : 0 < (N : ℝ) := by dsimp [N]; positivity
  let z : UnitBall W := ⟨0, by simp⟩
  refine ⟨(N : ℝ) + ‖f z‖, by positivity, fun x => ?_⟩
  let u (k : ℕ) (hk : k ≤ N) : UnitBall W :=
    ⟨(((k : ℝ) / (N : ℝ) : ℝ) : 𝕜) • x.val, by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
      exact (mul_le_mul_of_nonneg_right ((div_le_one hN).2 (by exact_mod_cast hk))
        (norm_nonneg x.val)).trans (by simpa only [one_mul] using x.property)⟩
  have hu (k : ℕ) (hk : k ≤ N) : dist (f (u k hk)) (f z) ≤ (k : ℝ) := by
    induction k with
    | zero => simp [u, z]
    | succ k ih =>
      have hk' : k ≤ N := (Nat.le_succ k).trans hk
      have hstep : dist (u (k + 1) hk) (u k hk') < δ := by
        rw [Subtype.dist_eq, dist_eq_norm]
        change ‖((((k + 1 : ℕ) : ℝ) / (N : ℝ) : ℝ) : 𝕜) • x.val -
          (((k : ℝ) / (N : ℝ) : ℝ) : 𝕜) • x.val‖ < δ
        rw [← sub_smul, ← RCLike.ofReal_sub]
        have hcoef : ((k + 1 : ℕ) : ℝ) / (N : ℝ) - (k : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by
          push_cast
          ring
        rw [hcoef, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
        exact (mul_le_mul_of_nonneg_left x.property (by positivity)).trans_lt
          (by simpa [N] using hn)
      calc
        dist (f (u (k + 1) hk)) (f z) ≤
            dist (f (u (k + 1) hk)) (f (u k hk')) + dist (f (u k hk')) (f z) :=
          dist_triangle _ _ _
        _ ≤ 1 + (k : ℝ) := add_le_add (hfδ hstep).le (ih hk')
        _ = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hlast : u N (le_refl _) = x := by
    apply Subtype.ext
    dsimp [u]
    rw [div_self hN.ne', RCLike.ofReal_one, one_smul]
  have hd : dist (f x) (f z) ≤ (N : ℝ) := by simpa only [hlast] using hu N (le_refl _)
  calc
    ‖f x‖ ≤ ‖f x - f z‖ + ‖f z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (f x - f z) (f z)
    _ ≤ (N : ℝ) + ‖f z‖ := add_le_add_right (by simpa only [dist_eq_norm] using hd) _

end LindenstraussRetraction
