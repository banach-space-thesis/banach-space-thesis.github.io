import Posets.AlspachCounterexampleLimit
import Posets.AlspachCounterexampleSuccessorContinuity

/-! At the ω stage the point and row spaces are one-point compactifications
of the punctured finite stages. The probability evaluations remain continuous
because every test function has uniformly small deviations on all but
finitely many summands. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology Filter
open scoped OnePoint
namespace Posets

theorem alspachOnePoint_finitely_many_large_spines {𝕜 I : Type*} [RCLike 𝕜]
    (X : I → Type*) [∀ i, TopologicalSpace (X i)]
    (f : C(OnePoint (Σ i, X i), 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset I, ∀ i ∉ s, ∀ x : X i, ‖f (⟨i, x⟩ : Σ i, X i) - f ∞‖ < ε := by
  have hc : IsCompact {z : Σ i, X i | ε ≤ ‖f z - f ∞‖} := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isCompact_iff]
    have he : (↑) '' {z : Σ i, X i | ε ≤ ‖f z - f ∞‖} =
        {z : OnePoint (Σ i, X i) | ε ≤ ‖f z - f ∞‖} := by
      ext z
      cases z with
      | infty => simp [not_le.mpr hε]
      | coe z => simp
    rw [he]
    exact (isClosed_le continuous_const (f.continuous.sub continuous_const).norm).isCompact
  obtain ⟨s, t, hs, _, he⟩ := IsCompact.sigma_exists_finite_sigma_eq _ hc
  refine ⟨hs.toFinset, ?_⟩
  intro i hi x
  by_contra hn
  have hm : (⟨i, x⟩ : Σ i, X i) ∈ {z : Σ i, X i | ε ≤ ‖f z - f ∞‖} := le_of_not_gt hn
  rw [← he] at hm
  exact hi (hs.mem_toFinset.mpr hm.1)

namespace AlspachPointedRows
variable {𝕜 : Type*} [RCLike 𝕜] {K I : ℕ → Type*}
  [∀ n, TopologicalSpace (K n)] [∀ n, TopologicalSpace (I n)]
  [∀ n, CompactSpace (K n)] [∀ n, T2Space (K n)]
  [∀ n, CompactSpace (I n)] [∀ n, T2Space (I n)]
variable (F : ∀ n, AlspachPointedRows 𝕜 (K n) (I n))

abbrev LimitPointSpace := OnePoint (Σ n, {x : K n // x ≠ (F n).point})
abbrev LimitIndexSpace := OnePoint (Σ n, {i : I n // i ≠ (F n).index})

def topologicalLimit : AlspachPointedRows 𝕜 (LimitPointSpace F) (LimitIndexSpace F) := limit F

theorem limitPoint_continuous (n : ℕ) :
    @Continuous (K n) (LimitPointSpace F) _ _ (limitPoint F n) := by
  have he : (limitPoint F n : K n → LimitPointSpace F) =
      OnePoint.map (Sigma.mk n) ∘ (alspachPunctureHomeomorph (F n).point).symm := by
    funext x
    by_cases hx : x = (F n).point
    · subst x; simp [limitPoint, OnePoint.infty, OnePoint.map]
    · simp [limitPoint, hx, alspachPunctureHomeomorph_symm_nonroot, OnePoint.some, OnePoint.map]
  rw [he]
  apply Continuous.comp _ (alspachPunctureHomeomorph (F n).point).symm.continuous
  apply OnePoint.continuous_map continuous_sigmaMk
  rw [coclosedCompact_eq_cocompact, coclosedCompact_eq_cocompact]
  exact IsClosedEmbedding.sigmaMk.tendsto_cocompact

def limitDeviation (f : C(LimitPointSpace F, 𝕜)) (n : ℕ) (i : I n) : 𝕜 :=
  ((F n).row i).eval (fun x => f (limitPoint F n x) - f ∞)

theorem limitDeviation_continuous (hF : ∀ n, (F n).ContinuousRows)
    (f : C(LimitPointSpace F, 𝕜)) (n : ℕ) : Continuous (limitDeviation F f n) :=
  hF n ⟨_, (f.continuous.comp (limitPoint_continuous F n)).sub continuous_const⟩

theorem limitDeviation_root (f : C(LimitPointSpace F, 𝕜)) (n : ℕ) :
    limitDeviation F f n (F n).index = 0 := by
  simp [limitDeviation, (F n).row_root, OnePoint.infty]

theorem limitDeviation_small (f : C(LimitPointSpace F, 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℕ, ∀ n ∉ s, ∀ i, ‖limitDeviation F f n i‖ ≤ ε := by
  obtain ⟨s, hs⟩ := alspachOnePoint_finitely_many_large_spines _ f hε
  refine ⟨s, ?_⟩
  intro n hn i
  apply AlspachProbability.norm_eval_le
  intro x _
  by_cases hx : x = (F n).point
  · subst x; simp only [limitPoint_root, OnePoint.infty, sub_self, norm_zero]; exact hε.le
  · simpa only [limitPoint, hx, ↓reduceDIte] using (hs n hn ⟨x, hx⟩).le

def limitDeviationCZero (hF : ∀ n, (F n).ContinuousRows) (f : C(LimitPointSpace F, 𝕜)) :
    JLMS.CZero 𝕜 (Σ n, {i : I n // i ≠ (F n).index}) :=
  alspachPuncturedSumCZero (fun n => (F n).index) (limitDeviation F f)
    (limitDeviation_continuous F hF f) (limitDeviation_root F f)
    (fun _ hε => limitDeviation_small F f hε)

theorem topologicalLimit_continuous (hF : ∀ n, (F n).ContinuousRows) :
    (topologicalLimit F).ContinuousRows := by
  intro f
  let d := limitDeviationCZero F hF f
  let e := JLMS.extendCZeroOnePoint d
  have he : (fun z => ((topologicalLimit F).row z).eval f) =
      (fun z : LimitIndexSpace F => f ∞ + e z) := by
    funext z
    cases z using OnePoint.rec with
    | infty => change f ∞ = f ∞ + 0; simp
    | coe z =>
        rcases z with ⟨n, i⟩
        change (((F n).row i).map (limitPoint F n)).eval f =
          f ∞ + limitDeviation F f n i
        simp only [AlspachProbability.eval_map, limitDeviation,
          AlspachProbability.eval_sub, AlspachProbability.eval_const]
        ring
  rw [he]
  exact continuous_const.add e.continuous

end AlspachPointedRows
end Posets



