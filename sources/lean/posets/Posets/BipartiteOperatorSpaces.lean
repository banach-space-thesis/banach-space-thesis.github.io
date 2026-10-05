import Posets.ScalarMatrixRows
import Posets.UltrafilterBimoduleFunctional

/-! Restriction and extension by zero on discrete c₀ spaces. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P Q : Type*}

def discreteEmbedding (e : P ↪ Q) : Discrete P ↪ Discrete Q where
  toFun x := ⟨e x.val⟩
  inj' := by rintro ⟨x⟩ ⟨y⟩ h; exact congrArg Discrete.mk (e.injective (Discrete.mk.inj h))

def discreteCZeroPullVector (e : P ↪ Q) (f : CZeroOn 𝕜 Q) : CZeroOn 𝕜 P where
  toFun x := f (discreteEmbedding e x)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    have hf := zero_at_infty f
    rw [cocompact_eq_cofinite] at hf ⊢
    exact hf.comp (discreteEmbedding e).injective.tendsto_cofinite

theorem discreteCZeroPullVector_norm_le (e : P ↪ Q) (f : CZeroOn 𝕜 Q) :
    ‖discreteCZeroPullVector e f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    (fun x => f.toBCF.norm_coe_le_norm (discreteEmbedding e x))

def discreteCZeroPull (e : P ↪ Q) : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P :=
  ({toFun := discreteCZeroPullVector e
    map_add' := by intro f g; ext x; rfl
    map_smul' := by intro a f; ext x; rfl} :
      CZeroOn 𝕜 Q →ₗ[𝕜] CZeroOn 𝕜 P).mkContinuous 1
    (fun f => by simpa only [one_mul] using discreteCZeroPullVector_norm_le e f)

@[simp] theorem discreteCZeroPull_apply (e : P ↪ Q) (f : CZeroOn 𝕜 Q) (x : Discrete P) :
    discreteCZeroPull e f x = f ⟨e x.val⟩ := rfl

def discreteCZeroPushValue (e : P ↪ Q) (f : CZeroOn 𝕜 P) (x : Discrete Q) : 𝕜 :=
  if h : x.val ∈ Set.range e then f ⟨Classical.choose h⟩ else 0

theorem discreteCZeroPushValue_image (e : P ↪ Q) (f : CZeroOn 𝕜 P) (p : P) :
    discreteCZeroPushValue e f ⟨e p⟩ = f ⟨p⟩ := by
  have hp : e p ∈ Set.range e := ⟨p, rfl⟩
  simp only [discreteCZeroPushValue, dif_pos hp]
  congr 1
  exact congrArg Discrete.mk (e.injective (Classical.choose_spec hp))

theorem discreteCZeroPushValue_outside (e : P ↪ Q) (f : CZeroOn 𝕜 P)
    (q : Q) (hq : q ∉ Set.range e) : discreteCZeroPushValue e f ⟨q⟩ = 0 := by
  simp only [discreteCZeroPushValue, dif_neg hq]

def discreteCZeroPushVector (e : P ↪ Q) (f : CZeroOn 𝕜 P) : CZeroOn 𝕜 Q where
  toFun := discreteCZeroPushValue e f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hf := Metric.tendsto_nhds.mp (zero_at_infty f) ε hε
    rw [cocompact_eq_cofinite] at hf ⊢
    have hfin := eventually_cofinite.mp hf
    filter_upwards [(hfin.image (discreteEmbedding e)).compl_mem_cofinite] with x hx
    by_cases hr : x.val ∈ Set.range e
    · have hp : dist (f ⟨Classical.choose hr⟩) 0 < ε := by
        by_contra hbad
        apply hx
        exact ⟨⟨Classical.choose hr⟩, hbad,
          congrArg Discrete.mk (Classical.choose_spec hr)⟩
      simpa only [discreteCZeroPushValue, dif_pos hr] using hp
    · simpa only [discreteCZeroPushValue, dif_neg hr, dist_self] using hε

theorem discreteCZeroPushVector_norm_le (e : P ↪ Q) (f : CZeroOn 𝕜 P) :
    ‖discreteCZeroPushVector e f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  change ‖discreteCZeroPushValue e f x‖ ≤ ‖f‖
  by_cases hx : x.val ∈ Set.range e
  · simpa only [discreteCZeroPushValue, dif_pos hx] using
      f.toBCF.norm_coe_le_norm ⟨Classical.choose hx⟩
  · simpa only [discreteCZeroPushValue, dif_neg hx, norm_zero] using norm_nonneg f

def discreteCZeroPush (e : P ↪ Q) : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 Q :=
  ({toFun := discreteCZeroPushVector e
    map_add' := by
      intro f g; ext x
      by_cases hx : x.val ∈ Set.range e <;>
        simp [discreteCZeroPushVector, discreteCZeroPushValue, hx]
    map_smul' := by
      intro a f; ext x
      by_cases hx : x.val ∈ Set.range e <;>
        simp [discreteCZeroPushVector, discreteCZeroPushValue, hx]} :
      CZeroOn 𝕜 P →ₗ[𝕜] CZeroOn 𝕜 Q).mkContinuous 1
    (fun f => by simpa only [one_mul] using discreteCZeroPushVector_norm_le e f)

@[simp] theorem discreteCZeroPush_image (e : P ↪ Q) (f : CZeroOn 𝕜 P) (p : P) :
    discreteCZeroPush e f ⟨e p⟩ = f ⟨p⟩ := discreteCZeroPushValue_image e f p

theorem discreteCZeroPush_outside (e : P ↪ Q) (f : CZeroOn 𝕜 P)
    (q : Q) (hq : q ∉ Set.range e) : discreteCZeroPush e f ⟨q⟩ = 0 :=
  discreteCZeroPushValue_outside e f q hq

def sumLeftEmbedding : P ↪ P ⊕ Q := ⟨Sum.inl, Sum.inl_injective⟩
def sumRightEmbedding : Q ↪ P ⊕ Q := ⟨Sum.inr, Sum.inr_injective⟩

abbrev sumCZeroInl : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 (P ⊕ Q) :=
  discreteCZeroPush sumLeftEmbedding
abbrev sumCZeroInr : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 (P ⊕ Q) :=
  discreteCZeroPush sumRightEmbedding
abbrev sumCZeroFst : CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 P :=
  discreteCZeroPull sumLeftEmbedding
abbrev sumCZeroSnd : CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 Q :=
  discreteCZeroPull sumRightEmbedding

@[simp] theorem sumCZeroInl_inl (f : CZeroOn 𝕜 P) (p : P) :
    sumCZeroInl (Q := Q) f ⟨Sum.inl p⟩ = f ⟨p⟩ := discreteCZeroPush_image _ _ _
@[simp] theorem sumCZeroInl_inr (f : CZeroOn 𝕜 P) (q : Q) :
    sumCZeroInl f ⟨Sum.inr q⟩ = 0 :=
  discreteCZeroPush_outside _ _ _ (by rintro ⟨p, hp⟩; cases hp)
@[simp] theorem sumCZeroInr_inl (f : CZeroOn 𝕜 Q) (p : P) :
    sumCZeroInr f ⟨Sum.inl p⟩ = 0 :=
  discreteCZeroPush_outside _ _ _ (by rintro ⟨q, hq⟩; cases hq)
@[simp] theorem sumCZeroInr_inr (f : CZeroOn 𝕜 Q) (q : Q) :
    sumCZeroInr (P := P) f ⟨Sum.inr q⟩ = f ⟨q⟩ := discreteCZeroPush_image _ _ _

@[simp] theorem sumCZeroFst_apply (f : CZeroOn 𝕜 (P ⊕ Q)) (p : Discrete P) :
    sumCZeroFst f p = f ⟨Sum.inl p.val⟩ := rfl
@[simp] theorem sumCZeroSnd_apply (f : CZeroOn 𝕜 (P ⊕ Q)) (q : Discrete Q) :
    sumCZeroSnd f q = f ⟨Sum.inr q.val⟩ := rfl

theorem sumCZero_decomposition (f : CZeroOn 𝕜 (P ⊕ Q)) :
    sumCZeroInl (sumCZeroFst f) + sumCZeroInr (sumCZeroSnd f) = f := by
  ext x
  rcases x with ⟨p | q⟩ <;> simp [sumLeftEmbedding, sumRightEmbedding]

@[simp] theorem sumCZeroFst_inl (f : CZeroOn 𝕜 P) :
    sumCZeroFst (sumCZeroInl (Q := Q) f) = f := by ext x; simp [sumLeftEmbedding, sumRightEmbedding]
@[simp] theorem sumCZeroSnd_inr (f : CZeroOn 𝕜 Q) :
    sumCZeroSnd (sumCZeroInr (P := P) f) = f := by ext x; simp [sumLeftEmbedding, sumRightEmbedding]
@[simp] theorem sumCZeroFst_inr (f : CZeroOn 𝕜 Q) :
    sumCZeroFst (sumCZeroInr (P := P) f) = 0 := by ext x; simp [sumLeftEmbedding, sumRightEmbedding]
@[simp] theorem sumCZeroSnd_inl (f : CZeroOn 𝕜 P) :
    sumCZeroSnd (sumCZeroInl (Q := Q) f) = 0 := by ext x; simp [sumLeftEmbedding, sumRightEmbedding]

end Posets

