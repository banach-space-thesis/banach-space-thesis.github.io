import JLMS.CZeroSumProduct
import JLMS.CZeroSumOperators
import JLMS.CZeroSumFubini
import JLMS.OrdinalSpaceSumAbsorption

/-!
# Adjacent absorption in a c₀ sum

This is the Banach-space rearrangement in Kislyakov Lemma 3.3. If the next
space in a sequence absorbs I copies of the preceding space uniformly,
then the sum of the sequence is isomorphic to I copies of itself. An outer
index set is allowed, so the same proof covers families of such sequences.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace JLMS
universe u u' v w
variable {𝕜 : Type w} [RCLike 𝕜]

local instance adjacentCZeroSumGroup {J : Type*} (F : J → Type*)
    [∀ j, NormedAddCommGroup (F j)] [∀ j, NormedSpace 𝕜 (F j)] :
    NormedAddCommGroup (CZeroSum 𝕜 F) := inferInstance
local instance adjacentCZeroSumSpace {J : Type*} (F : J → Type*)
    [∀ j, NormedAddCommGroup (F j)] [∀ j, NormedSpace 𝕜 (F j)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 F) := inferInstance

def natHeadIndexEquiv : PUnit.{1} ⊕ ℕ ≃ ℕ where
  toFun := Sum.elim (fun _ => 0) Nat.succ
  invFun n := match n with | 0 => .inl PUnit.unit | n + 1 => .inr n
  left_inv x := by cases x with | inl x => cases x; rfl | inr n => rfl
  right_inv n := by cases n <;> rfl

/-- Split the zeroth coordinate from a c₀ sequence of varying spaces. -/
def cZeroSumNatHeadIsometry (E : ℕ → Type v) [∀ n, NormedAddCommGroup (E n)]
    [∀ n, NormedSpace 𝕜 (E n)] :
    CZeroSum 𝕜 E ≃ₗᵢ[𝕜] E 0 × CZeroSum 𝕜 (fun n => E (n + 1)) :=
  (CZeroSum.reindex (𝕜 := 𝕜) (E := E) natHeadIndexEquiv).trans
    (CZeroSum.sumIsometry.trans
      (linearIsometryEquivProdCongr (cZeroSumSingletonIsometry (𝕜 := 𝕜) (E 0))
        (LinearIsometryEquiv.refl 𝕜 _)))

/-- A space whose tail absorbs I copies of the entire space is itself
isomorphic to those I copies. -/
def cZeroSumEquivOfTailReplication (I : Type u) [Infinite I]
    {S H T : Type*} [NormedAddCommGroup S] [NormedSpace 𝕜 S]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    (h : S ≃L[𝕜] H × T)
    (t : T ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => S) × T) :
    S ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => S) := by
  let X := CZeroSum 𝕜 (fun _ : I => S)
  let shuffle : (H × (X × T)) ≃L[𝕜] X × (H × T) :=
    (ContinuousLinearEquiv.prodAssoc 𝕜 H X T).symm.trans
      (((ContinuousLinearEquiv.prodComm 𝕜 H X).prodCongr (ContinuousLinearEquiv.refl 𝕜 T)).trans
        (ContinuousLinearEquiv.prodAssoc 𝕜 X H T))
  exact h.trans (((ContinuousLinearEquiv.refl 𝕜 H).prodCongr t).trans
    (shuffle.trans (((ContinuousLinearEquiv.refl 𝕜 X).prodCongr h.symm).trans
      ((ContinuousLinearEquiv.prodComm 𝕜 X S).trans
        (cZeroSumInfiniteHeadIsometry (𝕜 := 𝕜) I S).symm.toContinuousLinearEquiv))))

/-- Uniform adjacent absorption, including an arbitrary outer c₀ sum.
The bound is a distortion-product bound, as in Kislyakov Lemma 1.1. -/
theorem nonempty_cZeroSum_adjacentReplication (I : Type u) [Infinite I]
    {B : Type u'} (E : B → ℕ → Type v) [∀ b n, NormedAddCommGroup (E b n)]
    [∀ b n, NormedSpace 𝕜 (E b n)] {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ b n, ∃ e : E b (n + 1) ≃L[𝕜]
        CZeroSum 𝕜 (fun _ : I => E b n) × E b (n + 1),
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ K) :
    Nonempty ((CZeroSum 𝕜 (fun b => CZeroSum 𝕜 (E b))) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : I => CZeroSum 𝕜 (fun b => CZeroSum 𝕜 (E b)))) := by
  let S := CZeroSum 𝕜 (fun b => CZeroSum 𝕜 (E b))
  let H := CZeroSum 𝕜 (fun b => E b 0)
  let T := CZeroSum 𝕜 (fun b => CZeroSum 𝕜 (fun n => E b (n + 1)))
  let X := CZeroSum 𝕜 (fun _ : I => S)
  let h : S ≃ₗᵢ[𝕜] H × T :=
    (CZeroSum.congrRightIsometry (fun b => cZeroSumNatHeadIsometry (𝕜 := 𝕜) (E b))).trans
      CZeroSum.productIsometry
  let tflat := CZeroSum.prodIsometry (𝕜 := 𝕜) (E := fun b n => E b (n + 1))
  obtain ⟨L, _hL⟩ := CZeroSum.exists_congrRight_of_distortion
    (𝕜 := 𝕜) (I := B × ℕ)
    (E := fun p => E p.1 (p.2 + 1))
    (F := fun p => CZeroSum 𝕜 (fun _ : I => E p.1 p.2) × E p.1 (p.2 + 1))
    hK (fun p => he p.1 p.2)
  let uf : CZeroSum 𝕜 (fun p : B × ℕ => CZeroSum 𝕜 (fun _ : I => E p.1 p.2)) ≃ₗᵢ[𝕜] X :=
    (CZeroSum.commuteIsometry (𝕜 := 𝕜) (E := fun (p : B × ℕ) (_ : I) => E p.1 p.2)).trans
      (CZeroSum.congrRightIsometry (fun _ : I => (CZeroSum.prodIsometry (𝕜 := 𝕜) (E := E)).symm))
  let t : T ≃L[𝕜] X × T := tflat.toContinuousLinearEquiv.trans
    (L.trans (CZeroSum.productIsometry.toContinuousLinearEquiv.trans
      (uf.toContinuousLinearEquiv.prodCongr tflat.symm.toContinuousLinearEquiv)))
  exact ⟨cZeroSumEquivOfTailReplication I h.toContinuousLinearEquiv t⟩

end JLMS
