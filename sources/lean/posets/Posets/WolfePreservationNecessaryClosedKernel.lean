import Posets.WolfePreservationBlockFunctions
import ThesisCommon.Analysis.CountableMetricClopen

/-! Closed support relations defined by all clopen neighborhood tests.
Their fibres have a finite bound determined by the dual norm and the mass
threshold. The definition avoids claiming that a moving atomic coefficient
is itself upper semicontinuous for arbitrary signed or complex measures. -/

noncomputable section
open Set Filter Topology
namespace Posets

theorem wolfe_finite_disjoint_clopen_points {L : Type*} [MetricSpace L] [Countable L]
    (s : Finset L) :
    ∃ V : L → Set L, (∀ x, IsClopen (V x)) ∧ (∀ x ∈ s, x ∈ V x) ∧
      Pairwise (fun x y => Disjoint (V x) (V y)) ∧ ∀ x ∉ s, V x = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅, fun _ => isClopen_empty, by simp,
      fun _ _ _ => disjoint_bot_left, by simp⟩
  | @insert x s hxs ih =>
      obtain ⟨V, hV, hmem, hd, he⟩ := ih
      obtain ⟨U, hU, hxU, hUs⟩ := ThesisCommon.countableMetric_exists_clopen_nhds x
        (s.finite_toSet.isClosed.isOpen_compl.mem_nhds hxs)
      let W : L → Set L := fun y => if y = x then U else V y \ U
      refine ⟨W, ?_, ?_, ?_, ?_⟩
      · intro y
        by_cases hy : y = x
        · simpa only [W, if_pos hy] using hU
        · simpa only [W, if_neg hy] using (hV y).diff hU
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simpa [W] using hxU
        · have hyx : y ≠ x := fun heq => hxs (heq ▸ hy)
          simp only [W, if_neg hyx, mem_diff]
          exact ⟨hmem y hy, fun hyU => hUs hyU hy⟩
      · intro y z hyz
        by_cases hy : y = x
        · subst y
          simpa only [W, if_pos rfl, if_neg (Ne.symm hyz)] using
            (disjoint_sdiff_right (s := U) (t := V z))
        · by_cases hz : z = x
          · subst z
            simpa only [W, if_neg hy, if_pos rfl] using
              (disjoint_sdiff_left (s := U) (t := V y))
          · exact (hd hyz).mono (by simp [W, hy]) (by simp [W, hz])
      · intro y hy
        have hyx : y ≠ x := fun h => hy (h ▸ Finset.mem_insert_self x s)
        have hys : y ∉ s := fun h => hy (Finset.mem_insert_of_mem h)
        simp [W, hyx, he y hys]

section Relation
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace L] [CompactSpace L]

def wolfeClopenKernelRelation
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (d : ℝ) : Set (K × L) :=
  {p | ∀ (V : Set L) (hV : IsClopen V), p.2 ∈ V →
    d ≤ RCLike.re (ν p.1 (wolfeSourceBlock V hV))}

theorem wolfeClopenKernelRelation_isClosed
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (hν : Continuous ν) (d : ℝ) :
    IsClosed (wolfeClopenKernelRelation ν d) := by
  have heq : wolfeClopenKernelRelation ν d =
      ⋂ (V : Set L) (hV : IsClopen V),
        (Prod.snd ⁻¹' Vᶜ) ∪
          {p : K × L | d ≤ RCLike.re (ν p.1 (wolfeSourceBlock V hV))} := by
    ext p
    simp only [wolfeClopenKernelRelation, mem_setOf_eq, mem_iInter, mem_union,
      mem_preimage, mem_compl_iff]
    exact forall₂_congr fun V hV => imp_iff_not_or
  rw [heq]
  apply isClosed_iInter
  intro V
  apply isClosed_iInter
  intro hV
  exact (hV.compl.isClosed.preimage continuous_snd).union
    (isClosed_le continuous_const (RCLike.continuous_re.comp
      ((WeakDual.eval_continuous _).comp (hν.comp continuous_fst))))

end Relation

section Budget
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [MetricSpace L] [Countable L] [CompactSpace L]

local instance wolfeClosedKernelDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance
local instance wolfeClosedKernelDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance

theorem wolfeClopenKernelRelation_finite_budget
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (d : ℝ) (y : K)
    (s : Finset L) (hs : ∀ x ∈ s, (y, x) ∈ wolfeClopenKernelRelation ν d) :
    (s.card : ℝ) * d ≤ ‖WeakDual.toStrongDual (ν y)‖ := by
  classical
  obtain ⟨V, hV, hm, hd, _⟩ := wolfe_finite_disjoint_clopen_points s
  let f : JLMS.CZero 𝕜 L := ∑ x ∈ s, wolfeSourceBlock (V x) (hV x)
  have hf : ‖f‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro z
    have he (x : L) : wolfeSourceBlock (𝕜 := 𝕜) (V x) (hV x) z =
        if z ∈ V x then 1 else 0 := wolfeSourceBlock_apply _ _ _
    change ‖JLMS.evaluation z (∑ x ∈ s, wolfeSourceBlock (V x) (hV x))‖ ≤ 1
    simp only [map_sum, JLMS.evaluation_apply, he]
    by_cases hz : ∃ x ∈ s, z ∈ V x
    · obtain ⟨x, hxs, hzx⟩ := hz
      rw [Finset.sum_eq_single x]
      · simp [hzx]
      · intro w hw hwx
        have hzw : z ∉ V w := fun h => Set.disjoint_left.mp (hd hwx) h hzx
        simp [hzw]
      · exact fun h => (h hxs).elim
    · have hz' : ∀ x ∈ s, z ∉ V x := by simpa using hz
      simp only [Finset.sum_eq_zero (fun x hx => if_neg (hz' x hx)), norm_zero, zero_le_one]
  calc
    (s.card : ℝ) * d = ∑ _x ∈ s, d := by simp
    _ ≤ ∑ x ∈ s, RCLike.re (ν y (wolfeSourceBlock (V x) (hV x))) :=
      Finset.sum_le_sum fun x hx => hs x hx (V x) (hV x) (hm x hx)
    _ = RCLike.re (ν y f) := by simp [f, map_sum]
    _ ≤ ‖ν y f‖ := RCLike.re_le_norm _
    _ ≤ ‖WeakDual.toStrongDual (ν y)‖ * ‖f‖ :=
      (WeakDual.toStrongDual (ν y)).le_opNorm f
    _ ≤ ‖WeakDual.toStrongDual (ν y)‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (norm_nonneg _)

theorem wolfeClopenKernelRelation_uniform_finite_fibres
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L)) {C d : ℝ} (hd : 0 < d)
    (hbound : ∀ y, ‖WeakDual.toStrongDual (ν y)‖ ≤ C) :
    ∃ N : ℕ, ∀ y : K, ∀ s : Finset L,
      (∀ x ∈ s, (y, x) ∈ wolfeClopenKernelRelation ν d) → s.card ≤ N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (C / d)
  refine ⟨N, ?_⟩
  intro y s hs
  have hb := (wolfeClopenKernelRelation_finite_budget ν d y s hs).trans (hbound y)
  have hlt : (s.card : ℝ) < N := by
    apply (mul_lt_mul_iff_left₀ hd).mp
    exact hb.trans_lt ((div_lt_iff₀ hd).mp hN)
  exact (by exact_mod_cast hlt : s.card < N).le

end Budget
end Posets
