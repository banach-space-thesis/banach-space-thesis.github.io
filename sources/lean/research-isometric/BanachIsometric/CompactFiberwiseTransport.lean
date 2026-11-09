import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.ContinuousMap.Compact

/-! Finite-step transport through an actual fiberwise neighborhood retraction.
Compactness supplies a uniform tube and uniform continuity supplies one finite
time grid. Every step is a genuine continuous map into the prescribed fiber.
This constructs endpoint sections over compact contractions without assuming
a general fiber-bundle homotopy-lifting or classification theorem. -/

noncomputable section

namespace BanachIsometric

open Set Metric
open scoped Topology unitInterval

variable {B V A : Type*} [PseudoMetricSpace B] [PseudoMetricSpace V]

theorem exists_uniform_fiberwise_domain_radius {K U : Set (B × V)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b v, (b, v) ∈ K →
      ∀ b', dist b' b < ε → (b', v) ∈ U := by
  obtain ⟨ε, hε, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨ε, hε, ?_⟩
  intro b v hb b' hdist
  apply hsub
  apply Metric.mem_cthickening_of_dist_le (b', v) (b, v) ε K hb
  simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist b' b)] using hdist.le

def contractionTimeGrid (n k : ℕ) : I := projIcc 0 1 zero_le_one ((k : ℝ) / n)

@[simp] theorem contractionTimeGrid_zero (n : ℕ) : contractionTimeGrid n 0 = 0 := by
  simp [contractionTimeGrid]

theorem contractionTimeGrid_self {n : ℕ} (hn : 0 < n) : contractionTimeGrid n n = 1 := by
  simp [contractionTimeGrid, ne_of_gt hn]

theorem dist_contractionTimeGrid_succ (n k : ℕ) :
    dist (contractionTimeGrid n (k + 1)) (contractionTimeGrid n k) ≤ 1 / (n : ℝ) := by
  have h := (LipschitzWith.projIcc zero_le_one).dist_le_mul
    (((k + 1 : ℕ) : ℝ) / n) ((k : ℝ) / n)
  have he : (((k + 1 : ℕ) : ℝ) / n) - (k : ℝ) / n = 1 / (n : ℝ) := by
    push_cast
    ring
  have hnonneg : (0 : ℝ) ≤ 1 / (n : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg n)
  simpa only [contractionTimeGrid, NNReal.coe_one, one_mul, Real.dist_eq, he,
    abs_of_nonneg hnonneg] using h

def iterateFiberwiseRetraction (r : B × V → V) (F : I × A → B) (n : ℕ)
    (seed : A → V) : ℕ → A → V
  | 0 => seed
  | k + 1 => fun a => r (F (contractionTimeGrid n (k + 1), a),
      iterateFiberwiseRetraction r F n seed k a)

/-- Actual continuous endpoint transport through a compact fiber relation.
The retraction/domain assumptions here are the concrete data constructed by
`ExactSectionNeighborhood.lean` in the intended application. -/
theorem exists_continuous_endpoint_transport [PseudoMetricSpace A] [CompactSpace A]
    {K U : Set (B × V)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : B × V → V) (hr : ContinuousOn r U)
    (hvalid : ∀ t ∈ U, (t.1, r t) ∈ K)
    (hfix : ∀ t ∈ K, r t = t.2)
    (F : C(I × A, B)) (seed : C(A, V))
    (hseed : ∀ a, (F (0, a), seed a) ∈ K) :
    ∃ seed₁ : C(A, V), (∀ a, (F (1, a), seed₁ a) ∈ K) ∧
      ∀ a, (∀ t : I, F (t, a) = F (0, a)) → seed₁ a = seed a := by
  obtain ⟨ε, hε, htube⟩ := exists_uniform_fiberwise_domain_radius hK hU hKU
  have huc : UniformContinuous F := CompactSpace.uniformContinuous_of_continuous F.continuous
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  let n := N + 1
  have hn : 0 < n := Nat.succ_pos N
  have htime : 1 / (n : ℝ) < δ := by simpa only [n, Nat.cast_add, Nat.cast_one] using hN
  have hstep : ∀ (k : ℕ) (a : A),
      dist (F (contractionTimeGrid n (k + 1), a)) (F (contractionTimeGrid n k, a)) < ε := by
    intro k a
    apply hcontrol
    have hg := (dist_contractionTimeGrid_succ n k).trans_lt htime
    simpa only [Prod.dist_eq, dist_self,
      max_eq_left (dist_nonneg : 0 ≤ dist (contractionTimeGrid n (k + 1)) (contractionTimeGrid n k))] using hg
  have hiter : ∀ k, Continuous (iterateFiberwiseRetraction r F n seed k) ∧
      ∀ a, (F (contractionTimeGrid n k, a), iterateFiberwiseRetraction r F n seed k a) ∈ K := by
    intro k
    induction k with
    | zero => exact ⟨seed.continuous, by simpa only [iterateFiberwiseRetraction, contractionTimeGrid_zero] using hseed⟩
    | succ k ih =>
      have hmem : ∀ a, (F (contractionTimeGrid n (k + 1), a),
          iterateFiberwiseRetraction r F n seed k a) ∈ U := fun a =>
        htube _ _ (ih.2 a) _ (hstep k a)
      have hpair : Continuous (fun a => (F (contractionTimeGrid n (k + 1), a),
          iterateFiberwiseRetraction r F n seed k a)) :=
        (F.continuous.comp (continuous_const.prodMk continuous_id)).prodMk ih.1
      exact ⟨hr.comp_continuous hpair hmem, fun a => hvalid _ (hmem a)⟩
  have hfixed : ∀ k a, (∀ t : I, F (t, a) = F (0, a)) →
      iterateFiberwiseRetraction r F n seed k a = seed a := by
    intro k
    induction k with
    | zero => intro a _; rfl
    | succ k ih =>
      intro a ha
      change r (F (contractionTimeGrid n (k + 1), a),
        iterateFiberwiseRetraction r F n seed k a) = seed a
      rw [ih a ha]
      apply hfix
      rw [ha _]
      exact hseed a
  refine ⟨⟨iterateFiberwiseRetraction r F n seed n, (hiter n).1⟩, ?_, hfixed n⟩
  simpa only [contractionTimeGrid_self hn] using (hiter n).2

end BanachIsometric
