import BanachIsometric.BodyRetractionTransport
import BanachIsometric.ExactSectionTransitionLipschitz
import BanachIsometric.CompactLocalLipschitz

/-! Exact equivariant correction of a Lipschitz approximate section. -/

namespace BanachIsometric

open Set
open scoped NNReal

noncomputable section

namespace ExactSectionAtlas

variable {P E F : Type*} [PseudoMetricSpace P] [CompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H) (D : AmbientBodyRetraction S)

def correctedOperator (Y : P → E →L[ℝ] F) (i a : P) : E →L[ℝ] F :=
  (Z.forward i a).comp (D.retract ((Z.inverse i a).comp (Y a)))

omit [CompactSpace P] [FiniteDimensional ℝ E] in
theorem correctedOperator_valid (Y : P → E →L[ℝ] F) (i a : P)
    (ha : a ∈ Z.baseSet i) (hd : (Z.inverse i a).comp (Y a) ∈ D.domain) :
    Function.Injective (Z.correctedOperator D Y i a) ∧
      LinearMap.range (Z.correctedOperator D Y i a).toLinearMap = H a ∧
      Z.correctedOperator D Y i a '' S = K ∩ (H a : Set F) := by
  obtain ⟨hu, hb⟩ := D.range _ hd
  obtain ⟨u, hu⟩ := hu
  let g : bodyAutomorphismGroup S := ⟨u, by
    change (u : E →L[ℝ] E) '' S = S
    rw [hu]
    exact hb⟩
  have heq : Z.correctedOperator D Y i a = (exactBodyMapRight (Z.exactMap i a ha) g).val := by
    change (Z.forward i a).comp (D.retract _) = (Z.forward i a).comp (u : E →L[ℝ] E)
    rw [hu]
  rw [heq]
  exact (exactBodyMapRight (Z.exactMap i a ha) g).property

omit [CompactSpace P] [FiniteDimensional ℝ E] in
theorem correctedOperator_eq_on_overlap (Y : P → E →L[ℝ] F)
    (hY : ∀ a x, Y a x ∈ H a) (i j a : P)
    (hi : a ∈ Z.baseSet i) (hj : a ∈ Z.baseSet j) :
    Z.correctedOperator D Y i a = Z.correctedOperator D Y j a := by
  let g := Z.transition i j a
  have hcoord : (Z.inverse j a).comp (Y a) =
      (g.val : E →L[ℝ] E) * ((Z.inverse i a).comp (Y a)) := by
    rw [show (g.val : E →L[ℝ] E) = Z.transitionOperator i j a from Z.transition_val i j a ⟨hi, hj⟩]
    apply ContinuousLinearMap.ext
    intro x
    change Z.inverse j a (Y a x) = Z.inverse j a (Z.forward i a (Z.inverse i a (Y a x)))
    rw [Z.forward_inverse_apply i a hi _ (hY a x)]
  have hforward (x : E) : Z.forward j a ((g.val : E →L[ℝ] E) x) = Z.forward i a x := by
    rw [show (g.val : E →L[ℝ] E) = Z.transitionOperator i j a from Z.transition_val i j a ⟨hi, hj⟩]
    exact Z.forward_inverse_apply j a hj _ (Z.forward_mem_range i a hi x)
  apply ContinuousLinearMap.ext
  intro x
  change Z.forward i a (D.retract ((Z.inverse i a).comp (Y a)) x) =
    Z.forward j a (D.retract ((Z.inverse j a).comp (Y a)) x)
  rw [hcoord, D.equivariant]
  exact (hforward _).symm

omit [FiniteDimensional ℝ E] in
theorem exists_lipschitz_correctedOperator (Y : P → E →L[ℝ] F)
    {LY : ℝ≥0} (hY : LipschitzWith LY Y) (i : P)
    (hDomain : ∀ a ∈ Z.baseSet i, (Z.inverse i a).comp (Y a) ∈ D.domain) :
    ∃ L : ℝ≥0, LipschitzOnWith L (Z.correctedOperator D Y i) (Z.baseSet i) := by
  obtain ⟨KA, hA⟩ := Z.forward_lipschitz i
  obtain ⟨KB, hB⟩ := Z.inverse_lipschitz i
  obtain ⟨MA, hMA⟩ := exists_norm_bound_of_lipschitzOn_compact_base hA i (Z.mem_baseSet i)
  obtain ⟨MB, hMB⟩ := exists_norm_bound_of_lipschitzOn_compact_base hB i (Z.mem_baseSet i)
  obtain ⟨MY, hMY⟩ := exists_norm_bound_of_lipschitzOn_compact_base hY.lipschitzOnWith i (mem_univ i)
  have hCoord : LipschitzOnWith (MB * LY + KB * MY)
      (fun a => (Z.inverse i a).comp (Y a)) (Z.baseSet i) :=
    lipschitzOnWith_clm_comp hB hY.lipschitzOnWith (fun a ha => hMB a ha)
      (fun a _ => hMY a (mem_univ a))
  have hR : LipschitzOnWith (D.constant * (MB * LY + KB * MY))
      (fun a => D.retract ((Z.inverse i a).comp (Y a))) (Z.baseSet i) :=
    D.lipschitz.comp hCoord hDomain
  obtain ⟨MR, hMR⟩ := exists_norm_bound_of_lipschitzOn_compact_base hR i (Z.mem_baseSet i)
  exact ⟨MA * (D.constant * (MB * LY + KB * MY)) + KA * MR,
    lipschitzOnWith_clm_comp hA hR hMA hMR⟩

omit [FiniteDimensional ℝ E] in
/-- The equivariant correction patches to a global Lipschitz actual exact
section. The domain condition is later supplied by uniform approximation
to a continuous exact section, not assumed in the geometric wrapper. -/
theorem exists_lipschitz_exact_section_of_approximate
    (Y : P → E →L[ℝ] F) {LY : ℝ≥0} (hYLip : LipschitzWith LY Y)
    (hYRange : ∀ a x, Y a x ∈ H a) (I : Finset P)
    (hcover : ∀ a, ∃ i ∈ I, a ∈ Z.baseSet i)
    (hDomain : ∀ i ∈ I, ∀ a ∈ Z.baseSet i, (Z.inverse i a).comp (Y a) ∈ D.domain) :
    ∃ A : P → E →L[ℝ] F, ∃ L : ℝ≥0, LipschitzWith L A ∧
      ∀ a, Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H a ∧
        A a '' S = K ∩ (H a : Set F) := by
  classical
  choose chart hchartI hchart using hcover
  let A := fun a => Z.correctedOperator D Y (chart a) a
  have hLocalEq : ∀ i ∈ I, ∀ a ∈ Z.baseSet i, A a = Z.correctedOperator D Y i a := by
    intro i _ a ha
    exact Z.correctedOperator_eq_on_overlap D Y hYRange _ _ a (hchart a) ha
  have hLip : ∀ i : I, ∃ L : ℝ≥0, LipschitzOnWith L A (Z.baseSet i.val) := by
    intro i
    obtain ⟨L, hL⟩ := Z.exists_lipschitz_correctedOperator D Y hYLip i.val (hDomain i.val i.property)
    refine ⟨L, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro a ha b hb
    rw [hLocalEq i.val i.property a ha, hLocalEq i.val i.property b hb]
    exact hL.dist_le_mul a ha b hb
  choose L hL using hLip
  have hcover' : (⋃ i : I, Z.baseSet i.val) = univ := by
    apply eq_univ_of_forall
    intro a
    exact mem_iUnion.mpr ⟨⟨chart a, hchartI a⟩, hchart a⟩
  obtain ⟨C, hC⟩ := exists_lipschitzWith_of_finite_open_cover A
    (fun i : I => Z.baseSet i.val) (fun i => Z.isOpen_baseSet i.val) hcover' L hL
  exact ⟨A, C, hC, fun a => Z.correctedOperator_valid D Y (chart a) a (hchart a)
    (hDomain (chart a) (hchartI a) a (hchart a))⟩

end ExactSectionAtlas

end
end BanachIsometric
