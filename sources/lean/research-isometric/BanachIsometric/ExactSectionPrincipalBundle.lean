import BanachIsometric.ExactSectionAtlas

/-!
# Principal body-automorphism transition functions

The transition from chart `i` to chart `j` is the actual operator `B_j A_i`.
Its inverse, body preservation, cocycle law and continuity are proved from the
constructed atlas identities. These transitions define a Mathlib fiber bundle
core with fiber the genuine body-automorphism group.
-/

namespace BanachIsometric

open Set Filter Bundle
open scoped Topology NNReal

noncomputable section

namespace ExactSectionAtlas

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H)

def exactMap (i a : P) (ha : a ∈ Z.baseSet i) : ExactBodyMap S K (H a) :=
  ⟨Z.forward i a, Z.forward_valid i a ha⟩

omit [FiniteDimensional ℝ E] in
theorem forward_inverse_apply (i a : P) (ha : a ∈ Z.baseSet i)
    (y : F) (hy : y ∈ H a) : Z.forward i a (Z.inverse i a y) = y := by
  have hy' : y ∈ LinearMap.range (Z.forward i a).toLinearMap :=
    (Z.forward_valid i a ha).2.1.ge hy
  obtain ⟨x, rfl⟩ := hy'
  have h := congrArg (fun T : E →L[ℝ] E => T x) (Z.left_inverse i a ha)
  exact congrArg (Z.forward i a) h

omit [FiniteDimensional ℝ E] in
theorem forward_mem_range (i a : P) (ha : a ∈ Z.baseSet i) (x : E) :
    Z.forward i a x ∈ H a :=
  (Z.forward_valid i a ha).2.1.le (LinearMap.mem_range_self (Z.forward i a).toLinearMap x)

def transitionOperator (i j a : P) : E →L[ℝ] E :=
  (Z.inverse j a).comp (Z.forward i a)

omit [FiniteDimensional ℝ E] in
theorem transitionOperator_mul_reverse (i j a : P)
    (hi : a ∈ Z.baseSet i) (hj : a ∈ Z.baseSet j) :
    Z.transitionOperator i j a * Z.transitionOperator j i a = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change Z.inverse j a (Z.forward i a (Z.inverse i a (Z.forward j a x))) = x
  rw [Z.forward_inverse_apply i a hi _ (Z.forward_mem_range j a hj x)]
  exact congrArg (fun T : E →L[ℝ] E => T x) (Z.left_inverse j a hj)

omit [FiniteDimensional ℝ E] in
theorem transitionOperator_image_body (i j a : P)
    (hi : a ∈ Z.baseSet i) (hj : a ∈ Z.baseSet j) :
    Z.transitionOperator i j a '' S = S := by
  calc
    _ = Z.inverse j a '' (Z.forward i a '' S) := by rw [image_image]; rfl
    _ = Z.inverse j a '' (K ∩ (H a : Set F)) :=
      congrArg (Set.image (Z.inverse j a)) (Z.forward_valid i a hi).2.2
    _ = Z.inverse j a '' (Z.forward j a '' S) :=
      congrArg (Set.image (Z.inverse j a)) (Z.forward_valid j a hj).2.2.symm
    _ = S := by
      rw [image_image]
      have hfun : (fun x => Z.inverse j a (Z.forward j a x)) = id := by
        funext x
        exact congrArg (fun T : E →L[ℝ] E => T x) (Z.left_inverse j a hj)
      rw [hfun]
      exact image_id S

def transitionAt (i j a : P) (ha : a ∈ Z.baseSet i ∩ Z.baseSet j) : bodyAutomorphismGroup S :=
  ⟨⟨Z.transitionOperator i j a, Z.transitionOperator j i a,
    Z.transitionOperator_mul_reverse i j a ha.1 ha.2,
    Z.transitionOperator_mul_reverse j i a ha.2 ha.1⟩,
    Z.transitionOperator_image_body i j a ha.1 ha.2⟩

def transition (i j a : P) : bodyAutomorphismGroup S := by
  classical
  exact if ha : a ∈ Z.baseSet i ∩ Z.baseSet j then Z.transitionAt i j a ha else 1

omit [FiniteDimensional ℝ E] in
theorem transition_val (i j a : P) (ha : a ∈ Z.baseSet i ∩ Z.baseSet j) :
    ((Z.transition i j a).val : E →L[ℝ] E) = Z.transitionOperator i j a := by
  simp only [transition, dif_pos ha]
  rfl

omit [FiniteDimensional ℝ E] in
theorem transition_self (i a : P) (ha : a ∈ Z.baseSet i) : Z.transition i i a = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Z.transition_val i i a ⟨ha, ha⟩]
  exact Z.left_inverse i a ha

omit [FiniteDimensional ℝ E] in
theorem transition_cocycle (i j k a : P)
    (hi : a ∈ Z.baseSet i) (hj : a ∈ Z.baseSet j) (hk : a ∈ Z.baseSet k) :
    Z.transition j k a * Z.transition i j a = Z.transition i k a := by
  apply Subtype.ext
  apply Units.ext
  change ((Z.transition j k a).val : E →L[ℝ] E) *
      ((Z.transition i j a).val : E →L[ℝ] E) = ((Z.transition i k a).val : E →L[ℝ] E)
  rw [Z.transition_val j k a ⟨hj, hk⟩, Z.transition_val i j a ⟨hi, hj⟩,
    Z.transition_val i k a ⟨hi, hk⟩]
  apply ContinuousLinearMap.ext
  intro x
  change Z.inverse k a (Z.forward j a (Z.inverse j a (Z.forward i a x))) =
    Z.inverse k a (Z.forward i a x)
  rw [Z.forward_inverse_apply j a hj _ (Z.forward_mem_range i a hi x)]

theorem continuousOn_transition (i j : P) :
    ContinuousOn (Z.transition i j) (Z.baseSet i ∩ Z.baseSet j) := by
  obtain ⟨_, hA⟩ := Z.forward_lipschitz i
  obtain ⟨_, hB⟩ := Z.inverse_lipschitz j
  have hRaw : ContinuousOn (Z.transitionOperator i j) (Z.baseSet i ∩ Z.baseSet j) :=
    (hB.continuousOn.mono inter_subset_right).clm_comp
      (hA.continuousOn.mono inter_subset_left)
  have hEmb : Topology.IsEmbedding
      (fun g : bodyAutomorphismGroup S => (g.val : E →L[ℝ] E)) :=
    Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  apply hEmb.continuousOn_iff.mpr
  apply hRaw.congr
  intro a ha
  exact Z.transition_val i j a ha

/-- The genuine body-automorphism bundle core. Its cocycle is the actual
operator change of section coordinates, acting by left multiplication on the
right-torsor coordinates. -/
def fiberBundleCore : FiberBundleCore P P (bodyAutomorphismGroup S) where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := id
  mem_baseSet_at := Z.mem_baseSet
  coordChange i j a g := Z.transition i j a * g
  coordChange_self := by
    intro i a ha g
    rw [Z.transition_self i a ha, one_mul]
  continuousOn_coordChange := by
    intro i j
    have hT : ContinuousOn (fun p : P × bodyAutomorphismGroup S => Z.transition i j p.1)
        ((Z.baseSet i ∩ Z.baseSet j) ×ˢ univ) :=
      (Z.continuousOn_transition i j).comp continuous_fst.continuousOn (fun _ hp => hp.1)
    exact hT.mul continuous_snd.continuousOn
  coordChange_comp := by
    intro i j k a ha g
    rw [← mul_assoc, Z.transition_cocycle i j k a ha.1.1 ha.1.2 ha.2]

end ExactSectionAtlas

end
end BanachIsometric
