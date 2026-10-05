import ThesisCommon.Analysis.EllOneWeakCompact
import ThesisCommon.Analysis.KernelCutBound
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Disjoint measurable cutoffs define contractions from real L1 into ell-one.
Together with Schur compactness, this gives uniform decay of disjoint cutoffs
on actual weakly compact sets. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lOneCut_small_measure (f : Lp ℝ 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A, ∀ hA : MeasurableSet A,
      μ A ≤ ENNReal.ofReal δ → ‖lpCut A hA f‖ ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := (Lp.memLp f).eLpNorm_indicator_le le_rfl (by norm_num) hε
  refine ⟨δ, hδ, fun A hA hμA => ?_⟩
  change ‖((Lp.memLp f).indicator hA).toLp (A.indicator f)‖ ≤ ε
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (h A hA hμA)).trans_eq
    (ENNReal.toReal_ofReal hε.le)

theorem sum_norm_lOneCut_le (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) (f : Lp ℝ 1 μ) (F : Finset ℕ) :
    ∑ n ∈ F, ‖lpCut (A n) (hA n) f‖ ≤ ‖f‖ := by
  simp_rw [norm_lOneCut_eq_integral]
  rw [← integral_biUnion_finset F (fun n _ => hA n)
    (fun i _ j _ hij => hd hij) (fun _ _ => (L1.integrable_coeFn f).norm.integrableOn)]
  rw [L1.norm_eq_integral_norm]
  exact setIntegral_le_integral (L1.integrable_coeFn f).norm
    (Eventually.of_forall fun x => norm_nonneg (f x))

def disjointCutToEllOne (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) (φ : ℕ → (Lp ℝ 1 μ →L[ℝ] ℝ))
    (hφ : ∀ n, ‖φ n‖ ≤ 1) : Lp ℝ 1 μ →L[ℝ] CountableEllOne := by
  have hsum : ∀ f : Lp ℝ 1 μ, ∀ F : Finset ℕ,
      ∑ n ∈ F, ‖φ n (lpCut (A n) (hA n) f)‖ ≤ ‖f‖ := by
    intro f F
    apply le_trans (Finset.sum_le_sum fun n _ => (φ n).le_opNorm _ |>.trans ?_)
      (sum_norm_lOneCut_le A hA hd f F)
    exact mul_le_of_le_one_left (norm_nonneg _) (hφ n)
  let L : Lp ℝ 1 μ →ₗ[ℝ] CountableEllOne :=
    { toFun := fun f => ⟨fun n => φ n (lpCut (A n) (hA n) f),
        memℓp_gen' (by simpa only [ENNReal.toReal_one, Real.rpow_one] using hsum f)⟩
      map_add' := by intro f g; apply lp.ext; funext n; simp [lpCut_add]
      map_smul' := by intro c f; apply lp.ext; funext n; simp [lpCut_smul] }
  exact L.mkContinuous 1 (fun f => by
    simpa only [one_mul] using lp.norm_le_of_forall_sum_le
      (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (norm_nonneg f)
      (f := L f) (by simpa only [ENNReal.toReal_one, Real.rpow_one] using hsum f))

theorem disjointCutToEllOne_apply (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) (φ : ℕ → (Lp ℝ 1 μ →L[ℝ] ℝ))
    (hφ : ∀ n, ‖φ n‖ ≤ 1) (f : Lp ℝ 1 μ) (n : ℕ) :
    disjointCutToEllOne A hA hd φ hφ f n = φ n (lpCut (A n) (hA n) f) := rfl

theorem weakCompact_lOne_disjointCut
    {K : Set (WeakSpace ℝ (Lp ℝ 1 μ))} (hK : IsCompact K)
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A))
    (f : ℕ → Lp ℝ 1 μ) (hf : ∀ n, toWeakSpace ℝ (Lp ℝ 1 μ) (f n) ∈ K) :
    Tendsto (fun n => ‖lpCut (A n) (hA n) (f n)‖) atTop (𝓝 0) := by
  choose φ hφ hnorm using fun n => exists_dual_vector'' ℝ (lpCut (A n) (hA n) (f n))
  let T := disjointCutToEllOne A hA hd φ hφ
  have hc := isCompact_norm_of_weakEllOne (hK.image (WeakSpace.map T).continuous)
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (norm_nonneg _)
  · intro ε hε
    obtain ⟨N, hN⟩ := isCompact_ellOne_uniform_coordinates hc hε
    apply eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have htmem : T (f n) ∈ (toWeakSpace ℝ CountableEllOne).symm ''
        (WeakSpace.map T '' K) :=
      ⟨_, ⟨toWeakSpace ℝ (Lp ℝ 1 μ) (f n), hf n, rfl⟩, rfl⟩
    have hh := hN (T (f n)) htmem n hn
    simpa [T, disjointCutToEllOne_apply, hnorm] using hh

end ThesisCommon
