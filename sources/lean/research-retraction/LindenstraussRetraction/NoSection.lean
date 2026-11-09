import LindenstraussRetraction.Correction
import LindenstraussRetraction.NoSectionGeometry

/-!
# The concrete uniformly continuous section obstruction

We prove the special case needed by the manuscript directly for an ℓ₁ sum
of proper normed spaces. Interlaced averages of finite prefixes in `c₀`
have arbitrarily small distance. Their section images have an iterated
distance type whose escaped norm mass is both large and small.
-/

noncomputable section

open Filter Topology
open scoped ENNReal

namespace LindenstraussRetraction

universe u v w

variable {𝕜 : Type w} [RCLike 𝕜]
variable {I : Type u} {B : I → Type v}
variable [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace 𝕜 (B i)]
variable [∀ i, ProperSpace (B i)]

/-- No norm-at-most-one linear map from an ℓ₁ sum of proper normed spaces
onto `c₀` admits a uniformly continuous section on its unit ball. -/
theorem no_uniformSection_l1_c0
    (q : lp B 1 →L[𝕜] C0 𝕜) (hq : ‖q‖ ≤ 1) :
    ¬ HasUniformSectionOnUnitBall q := by
  intro hsection
  obtain ⟨s, hs, hright⟩ := hsection
  obtain ⟨C, hC, hsC⟩ := uniformContinuous_unitBall_norm_bounded (𝕜 := 𝕜) s hs
  obtain ⟨δ, hδ, hsδ⟩ := (Metric.uniformContinuous_iff.1 hs) (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let k : ℕ := n + 1
  have hk : 0 < k := Nat.succ_pos n
  have hkδ : 1 / (k : ℝ) < δ := by simpa only [k, Nat.cast_add, Nat.cast_one] using hn
  let av : (Fin k → ℕ) → UnitBall (C0 𝕜) :=
    fun a => ⟨prefixAverage 𝕜 a, norm_prefixAverage_le_one 𝕜 a⟩
  let F : (Fin k → ℕ) → L1MetricType B := fun a => L1MetricType.ofPoint (s (av a))
  have hF : ∀ a, (F a).mass ≤ C := fun a => hsC (av a)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  let T : L1MetricType B := L1MetricType.iteratedLimit U C k F
  have hqv (z : lp B 1) : ‖q z‖ ≤ ‖z‖ :=
    (q.le_opNorm z).trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hq (norm_nonneg z))
  have hsmall : T.distance T ≤ 1 / 2 := by
    have hbound : ∀ a : Fin (2 * k) → ℕ,
        L1MetricType.alternatingKernel k F F a ∈ Set.Icc 0 (2 * C) := by
      intro a
      refine ⟨L1MetricType.distance_nonneg _ _, ?_⟩
      exact (L1MetricType.distance_le_mass _ _).trans (by
        linarith [hF (evenCoordinates k a), hF (oddCoordinates k a)])
    have hlim := scalarIteratedLimit_le_of_increasing U hU (2 * k)
      (L1MetricType.alternatingKernel k F F) hbound 0 (fun a ha => by
        have hd : dist (av (evenCoordinates k a)) (av (oddCoordinates k a)) < δ := by
          rw [Subtype.dist_eq, dist_eq_norm]
          exact (norm_prefixAverage_interlaced_sub_le 𝕜 a ha.strictMono).trans_lt hkδ
        simpa only [L1MetricType.alternatingKernel, F,
          L1MetricType.distance_ofPoint, dist_eq_norm] using (hsδ hd).le)
    rw [L1MetricType.scalarIteratedLimit_alternatingKernel,
      L1MetricType.alternatingDistanceLimit_eq U C k F F hF hF] at hlim
    exact hlim
  let g : lp B 1 := T.point
  have hvanish : Tendsto (q g) atTop (𝓝 (0 : 𝕜)) := by
    have h := zero_at_infty (q g)
    rwa [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at h
  obtain ⟨j, hj⟩ := ((Metric.tendsto_nhds.1 hvanish) (1 / 4) (by norm_num)).exists
  have hj' : ‖(q g) j‖ < 1 / 4 := by simpa only [dist_zero_right] using hj
  have hlargeCoordinate : 3 / 4 ≤ ‖(1 : 𝕜) - (q g) j‖ := by
    have htriangle := norm_add_le ((1 : 𝕜) - (q g) j) ((q g) j)
    simp only [sub_add_cancel, norm_one] at htriangle
    linarith
  have hlarge : 3 / 4 ≤ T.distance (L1MetricType.ofPoint g) := by
    have hbound : ∀ a : Fin k → ℕ,
        (F a).distance (L1MetricType.ofPoint g) ∈ Set.Icc 0 (C + ‖g‖) := by
      intro a
      refine ⟨L1MetricType.distance_nonneg _ _, ?_⟩
      exact (L1MetricType.distance_le_mass _ _).trans (by
        simpa only [L1MetricType.ofPoint] using add_le_add_right (hF a) ‖g‖)
    have hlim := scalarIteratedLimit_ge_of_increasing U hU k
      (fun a => (F a).distance (L1MetricType.ofPoint g)) hbound j (fun a ha => by
        have hcoord : ‖(1 : 𝕜) - (q g) j‖ ≤ ‖s (av a) - g‖ := by
          calc
            ‖(1 : 𝕜) - (q g) j‖ = ‖(q (s (av a) - g)) j‖ := by
              rw [map_sub, hright]
              change ‖(1 : 𝕜) - (q g) j‖ = ‖prefixAverage 𝕜 a j - (q g) j‖
              rw [prefixAverage_apply_eq_one 𝕜 hk a j (fun i => ha.all_ge i)]
            _ ≤ ‖q (s (av a) - g)‖ := norm_c0Coordinate_apply_le 𝕜 j _
            _ ≤ ‖s (av a) - g‖ := hqv _
        simpa only [F, L1MetricType.distance_ofPoint] using hlargeCoordinate.trans hcoord)
    rw [L1MetricType.scalarIteratedLimit_distance_eq U C k F hF] at hlim
    exact hlim
  dsimp [L1MetricType.distance, L1MetricType.ofPoint, g] at hlarge hsmall
  simp only [sub_self, norm_zero, sub_self, add_zero, zero_add] at hlarge hsmall
  linarith

/-- The summation operator used in Section 4 has no uniformly continuous
section on the closed unit ball of `c₀`. -/
theorem no_uniformSection_summationOperator (𝕜 : Type w) [RCLike 𝕜] :
    ¬ HasUniformSectionOnUnitBall (summationOperator 𝕜) :=
  no_uniformSection_l1_c0 (summationOperator 𝕜) (norm_summationOperator_le 𝕜)

end LindenstraussRetraction
