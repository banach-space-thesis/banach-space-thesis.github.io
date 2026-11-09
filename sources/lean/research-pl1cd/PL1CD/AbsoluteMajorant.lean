import PL1CD.AbsoluteOperatorLimit
import PL1CD.PositiveVanishing

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators

namespace PL1CD.HaarPartitions
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.PositiveHaarOperators PL1CD.L1Order
open PL1CD.CylinderRefinement

theorem absoluteOperator_self_atom (B : HaarL1 →L[ℝ] HaarL1)
    (S : Finset ℕ) (a : Assignments S) : absoluteOperator B S (atom S a) = absL1 (B (atom S a)) := by
  classical
  rw [absoluteOperator_atom B S S (Finset.Subset.refl S) a]
  have he (b : Assignments S) : restrict S S (Finset.Subset.refl S) b = b := rfl
  simp_rw [he]
  simp

theorem absoluteOperator_ge_abs_atom (B : HaarL1 →L[ℝ] HaarL1)
    (S V : Finset ℕ) (hVS : V ⊆ S) (a : Assignments V) :
    ∀ᵐ x ∂haar, absL1 (B (atom V a)) x ≤ absoluteOperator B S (atom V a) x := by
  let T := S \ V
  have hd : Disjoint V T := Finset.disjoint_left.mpr (fun j hj ht =>
    (Finset.mem_sdiff.mp ht).2 hj)
  have he : V ∪ T = S := Finset.union_sdiff_of_subset hVS
  simpa only [he, absoluteOperator_self_atom] using
    absoluteOperator_refinement_le B V T V hd (Finset.Subset.refl V) a

theorem limit_dominates_atoms (B Q : HaarL1 →L[ℝ] HaarL1)
    (hQ : ∀ f, Tendsto (fun r => absoluteOperator B (Finset.range r) f) atTop (𝓝 (Q f)))
    (k : ℕ) (a : Assignments (Finset.range k)) :
    ∀ᵐ x ∂haar, absL1 (B (atom (Finset.range k) a)) x ≤ Q (atom (Finset.range k) a) x := by
  let f := atom (Finset.range k) a
  have hp (r : ℕ) : Nonneg (absoluteOperator B (Finset.range (k + r)) f - absL1 (B f)) := by
    filter_upwards [absoluteOperator_ge_abs_atom B (Finset.range (k + r)) (Finset.range k)
      (Finset.range_mono (by omega)) a,
      Lp.coeFn_sub (absoluteOperator B (Finset.range (k + r)) f) (absL1 (B f))]
      with x hx hs
    rw [hs, Pi.sub_apply]
    linarith
  have ht : Tendsto (fun r => absoluteOperator B (Finset.range (k + r)) f - absL1 (B f))
      atTop (𝓝 (Q f - absL1 (B f))) :=
    ((hQ f).comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat k)).sub_const _
  have hn := nonneg_of_tendsto _ _ hp ht
  filter_upwards [hn, Lp.coeFn_sub (Q f) (absL1 (B f))] with x hx hs
  rw [hs, Pi.sub_apply] at hx
  linarith

theorem nonneg_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → HaarL1)
    (hc : ∀ i, 0 ≤ c i) (hf : ∀ i, Nonneg (f i)) : Nonneg (∑ i ∈ s, c i • f i) := by
  classical
  have hsm : ∀ᵐ x ∂haar, ∀ i ∈ s, (c i • f i) x = c i * f i x :=
    s.eventually_all.mpr (fun i _ => (Lp.coeFn_smul (c i) (f i)).mono
      (fun x hx => by simpa only [Pi.smul_apply, smul_eq_mul] using hx))
  have hp : ∀ᵐ x ∂haar, ∀ i ∈ s, 0 ≤ f i x := s.eventually_all.mpr (fun i _ => hf i)
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun i => c i • f i), hsm, hp] with x hs hm hp
  rw [hs]
  exact Finset.sum_nonneg (fun i hi => (hm i hi).symm ▸ mul_nonneg (hc i) (hp i hi))

theorem positive_on_lifts_of_positive_on_atoms (D : HaarL1 →L[ℝ] HaarL1)
    (hD : ∀ k (a : Assignments (Finset.range k)), Nonneg (D (atom (Finset.range k) a)))
    (k : ℕ) (g : PL1.Bonami.Cube k → ℝ) (hg : Nonneg (PL1CD.Entropy.liftLp k g)) :
    Nonneg (D (PL1CD.Entropy.liftLp k g)) := by
  rw [liftLp_atom_sum, map_sum]
  simp_rw [map_smul]
  exact nonneg_sum_smul Finset.univ _ _
    (fun a => (liftLp_nonneg_iff k g).mp hg _) (hD k)

theorem expectation_positive (k : ℕ) : IsPositive (PL1.WalshExpectations.expectationL1 ℝ k) := by
  intro f hf
  let ν := PL1.WalshExpectations.tailMeasure k
  have hb := (measurePreserving_multiply ν).quasiMeasurePreserving.ae hf
  filter_upwards [coeFn_convolutionL1 ν f, Measure.ae_ae_of_ae_prod hb] with x hx hp
  change 0 ≤ convolutionL1 ν f x
  rw [hx]
  exact integral_nonneg_of_ae hp

theorem positive_of_positive_on_atoms (D : HaarL1 →L[ℝ] HaarL1)
    (hD : ∀ k (a : Assignments (Finset.range k)), Nonneg (D (atom (Finset.range k) a))) :
    IsPositive D := by
  intro f hf
  have hp (k : ℕ) : Nonneg (D (PL1.WalshExpectations.expectationL1 ℝ k f)) := by
    obtain ⟨g, hg⟩ := PL1CD.Entropy.exists_lift_of_finiteSpan k _
      (PL1.WalshExpectations.expectationL1_mem_finiteSpan ℝ k f)
    rw [← hg]
    exact positive_on_lifts_of_positive_on_atoms D hD k g
      (by rw [hg]; exact expectation_positive k f hf)
  exact nonneg_of_tendsto _ _ hp
    ((D.continuous.tendsto f).comp (PL1.WalshExpectations.tendsto_expectationL1 ℝ f))

theorem exists_positive_decomposition (B : HaarL1 →L[ℝ] HaarL1) :
    ∃ P N : HaarL1 →L[ℝ] HaarL1, IsPositive P ∧ IsPositive N ∧ B = P - N := by
  obtain ⟨Q, _, _, hQ⟩ := exists_absoluteOperator_limit B
  have hplus : IsPositive (Q + B) := by
    apply positive_of_positive_on_atoms
    intro k a
    filter_upwards [limit_dominates_atoms B Q hQ k a, coeFn_absL1 (B (atom _ a)),
      Lp.coeFn_add (Q (atom _ a)) (B (atom _ a))] with x hd ha hs
    change 0 ≤ (Q (atom _ a) + B (atom _ a)) x
    rw [hs, Pi.add_apply]
    rw [ha] at hd
    linarith [neg_le_abs (B (atom _ a) x)]
  have hminus : IsPositive (Q - B) := by
    apply positive_of_positive_on_atoms
    intro k a
    filter_upwards [limit_dominates_atoms B Q hQ k a, coeFn_absL1 (B (atom _ a)),
      Lp.coeFn_sub (Q (atom _ a)) (B (atom _ a))] with x hd ha hs
    change 0 ≤ (Q (atom _ a) - B (atom _ a)) x
    rw [hs, Pi.sub_apply]
    rw [ha] at hd
    linarith [le_abs_self (B (atom _ a) x)]
  refine ⟨(1 / 2 : ℝ) • (Q + B), (1 / 2 : ℝ) • (Q - B),
    hplus.smul _ (by norm_num), hminus.smul _ (by norm_num), ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply]
  module

end PL1CD.HaarPartitions
