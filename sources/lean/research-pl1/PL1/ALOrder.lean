import PL1.ALRenorming
import PL1.LatticeStrictPositive
import BanLat.Substructures.Band.PPP

/-!
# Monotone completeness from an AL norm

Positive additivity alone supplies the norming positive functional and norm
convergence of bounded monotone nets. No Schur-property premise is used.
-/

noncomputable section
open Filter
open scoped Topology

namespace PL1.ALOrder

open ALRenorming

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

def normLinear (hAL : IsALNorm E) : E →ₗ[ℝ] ℝ :=
  Positive.extension (fun x _ => norm_nonneg x) hAL

theorem normLinear_nonneg (hAL : IsALNorm E) {x : E} (hx : 0 ≤ x) :
    normLinear hAL x = ‖x‖ := Positive.extension_nonneg _ _ hx

theorem normLinear_positive (hAL : IsALNorm E) : Positive (normLinear hAL) :=
  Positive.extension_positive _ _

theorem abs_normLinear_le (hAL : IsALNorm E) (x : E) : |normLinear hAL x| ≤ ‖x‖ := by
  have h := Positive.abs_le_map_abs (normLinear_positive hAL) x
  rwa [normLinear_nonneg hAL (abs_nonneg x), norm_abs_eq_norm] at h

/-- The positive functional whose value on every positive vector is its norm. -/
def normFunctional (hAL : IsALNorm E) : E →L[ℝ] ℝ :=
  (normLinear hAL).mkContinuous 1 (fun x => by
    simpa only [Real.norm_eq_abs, one_mul] using abs_normLinear_le hAL x)

@[simp] theorem normFunctional_nonneg (hAL : IsALNorm E) {x : E} (hx : 0 ≤ x) :
    normFunctional hAL x = ‖x‖ := normLinear_nonneg hAL hx

theorem normFunctional_strictlyPositive (hAL : IsALNorm E) :
    SchurLattice.IsStrictlyPositive (normFunctional hAL) := by
  intro x hx
  rw [normFunctional_nonneg hAL hx.le]
  exact norm_pos_iff.mpr (ne_of_gt hx)

theorem norm_sub_of_le (hAL : IsALNorm E) {x y : E} (hxy : x ≤ y) :
    ‖y - x‖ = normFunctional hAL y - normFunctional hAL x := by
  rw [← map_sub, normFunctional_nonneg hAL (sub_nonneg.mpr hxy)]

private theorem cauchy_map_atTop_of_near_base {ι Y : Type*}
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [PseudoMetricSpace Y]
    (x : ι → Y)
    (h : ∀ ε : ℝ, 0 < ε → ∃ i, ∀ j, i ≤ j → dist (x j) (x i) < ε) :
    Cauchy (Filter.map x atTop) := by
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  obtain ⟨i, hi⟩ := h (ε / 2) (half_pos hε)
  refine ⟨x '' Set.Ici i, Filter.image_mem_map (Ici_mem_atTop i), ?_⟩
  rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
  have hj' := hi j hj
  have hk' := hi k hk
  have ht := dist_triangle (x j) (x i) (x k)
  rw [dist_comm (x i) (x k)] at ht
  linarith

/-- Every norm-bounded monotone directed net converges in a complete AL space. -/
theorem exists_tendsto_of_monotone_net_norm_bounded [CompleteSpace E]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (hAL : IsALNorm E) (x : ι → E) (hmono : Monotone x)
    (M : ℝ) (hM : ∀ i, ‖x i‖ ≤ M) : ∃ a : E, Tendsto x atTop (𝓝 a) := by
  let f : ι → ℝ := fun i => normFunctional hAL (x i)
  have hm : Monotone f := (Positive.monotone_iff.mpr (normLinear_positive hAL)).comp hmono
  have hb : BddAbove (Set.range f) := ⟨M, by
    rintro _ ⟨i, rfl⟩
    exact (le_abs_self (f i)).trans ((abs_normLinear_le hAL (x i)).trans (hM i))⟩
  have ht : Tendsto f atTop (𝓝 (⨆ i, f i)) := tendsto_atTop_ciSup hm hb
  apply cauchy_map_iff_exists_tendsto.mp
  apply cauchy_map_atTop_of_near_base
  intro ε hε
  have he : ∀ᶠ i in atTop, dist (f i) (⨆ j, f j) < ε / 2 :=
    (Metric.tendsto_nhds.mp ht) _ (half_pos hε)
  obtain ⟨i, hi⟩ := eventually_atTop.1 he
  refine ⟨i, fun j hij => ?_⟩
  have hd : dist (f j) (f i) < ε := by
    have hh := dist_triangle (f j) (⨆ k, f k) (f i)
    rw [dist_comm (⨆ k, f k) (f i)] at hh
    linarith [hi j hij, hi i le_rfl]
  rw [dist_eq_norm, norm_sub_of_le hAL (hmono hij)]
  exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq] using hd)

theorem exists_tendsto_of_antitone_net_norm_bounded [CompleteSpace E]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (hAL : IsALNorm E) (x : ι → E) (hanti : Antitone x)
    (M : ℝ) (hM : ∀ i, ‖x i‖ ≤ M) : ∃ a : E, Tendsto x atTop (𝓝 a) := by
  obtain ⟨a, ha⟩ := exists_tendsto_of_monotone_net_norm_bounded hAL (fun i => -x i)
    (fun i j hij => neg_le_neg (hanti hij)) M (fun i => by simpa using hM i)
  exact ⟨-a, by simpa only [neg_neg] using ha.neg⟩

/-- The actual existing order of a complete AL space is Dedekind complete. -/
@[reducible] def conditionallyCompleteLattice [CompleteSpace E] (hAL : IsALNorm E) :
    ConditionallyCompleteLattice E :=
  conditionallyCompleteLatticeOfPosNet E (by
    intro ι _ _ _ x hmono hx hbdd
    obtain ⟨b, hb⟩ := hbdd
    obtain ⟨a, ha⟩ := exists_tendsto_of_monotone_net_norm_bounded hAL x hmono ‖b‖ (by
      intro i
      apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg (hx i)]
      exact (hb (Set.mem_range_self i)).trans (le_abs_self b))
    exact ⟨a, isLUB_of_tendsto_atTop hmono ha⟩)

theorem conditionallyCompleteLattice_toLattice [CompleteSpace E] (hAL : IsALNorm E) :
    (conditionallyCompleteLattice hAL).toLattice = (inferInstance : Lattice E) := rfl

theorem exists_isLUB [CompleteSpace E] (hAL : IsALNorm E)
    (s : Set E) (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ a, IsLUB s a := by
  let := conditionallyCompleteLattice hAL
  exact ⟨sSup s, isLUB_csSup hne hbdd⟩

theorem tendsto_zero_of_antitone_net_isGLB [CompleteSpace E]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (hAL : IsALNorm E) (x : ι → E) (hanti : Antitone x)
    (hglb : IsGLB (Set.range x) 0) : Tendsto x atTop (𝓝 0) := by
  classical
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder (Set.Ici i₀) := ⟨fun i j => by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge (i : ι) (j : ι)
    exact ⟨⟨k, i.prop.trans hik⟩, hik, hjk⟩⟩
  let y : Set.Ici i₀ → E := fun i => x i
  have hy : Antitone y := fun i j hij => hanti hij
  have hx : ∀ i, 0 ≤ x i := fun i => hglb.1 (Set.mem_range_self i)
  obtain ⟨a, ha⟩ := exists_tendsto_of_antitone_net_norm_bounded hAL y hy ‖x i₀‖ (by
    intro i
    apply norm_le_norm_of_abs_le_abs
    simpa only [y, abs_of_nonneg (hx i), abs_of_nonneg (hx i₀)] using hanti i.prop)
  have htail : Tendsto x atTop (𝓝 a) := tendsto_comp_val_Ici_atTop.mp ha
  have heq : a = 0 := (isGLB_of_tendsto_atTop hanti htail).unique hglb
  exact heq ▸ htail

/-- An actual projection band for a prescribed band of the original lattice. -/
def bandOfAL [CompleteSpace E] (hAL : IsALNorm E) (B : Band E) : ProjectionBand E :=
  Classical.choose ((ProjectionBand.projectionBand_iff_isLUB_inter_Icc B).mpr (by
    intro x hx
    exact exists_isLUB hAL _
      ⟨0, B.toSubmodule.zero_mem, le_rfl, hx⟩ ⟨x, fun _ hy => hy.2.2⟩))

theorem bandOfAL_coe [CompleteSpace E] (hAL : IsALNorm E) (B : Band E) :
    (bandOfAL hAL B : Set E) = (B : Set E) :=
  Classical.choose_spec ((ProjectionBand.projectionBand_iff_isLUB_inter_Icc B).mpr (by
    intro x hx
    exact exists_isLUB hAL _
      ⟨0, B.toSubmodule.zero_mem, le_rfl, hx⟩ ⟨x, fun _ hy => hy.2.2⟩))

def principalBand [CompleteSpace E] (hAL : IsALNorm E) (a : E) : ProjectionBand E :=
  bandOfAL hAL (Band.generated ({a} : Set E))

theorem principalBand_coe [CompleteSpace E] (hAL : IsALNorm E) (a : E) :
    (principalBand hAL a : Set E) = (Band.generated ({a} : Set E) : Set E) :=
  bandOfAL_coe hAL _

theorem mem_principalBand_self [CompleteSpace E] (hAL : IsALNorm E) (a : E) :
    a ∈ principalBand hAL a := by
  change a ∈ (principalBand hAL a : Set E)
  rw [principalBand_coe]
  exact Band.subset_generated _ (Set.mem_singleton a)

end PL1.ALOrder
