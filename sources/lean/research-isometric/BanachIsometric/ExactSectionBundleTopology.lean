import BanachIsometric.ExactSectionPrincipalBundle

/-!
# Natural operator topology of the actual exact-section bundle

The total space here is the actual subset of the product of the parameter
space and the space of continuous linear operators. Its inherited topology
is identified with the topology of the constructed Mathlib bundle core.
-/

namespace BanachIsometric

open Set Filter Bundle
open scoped Topology NNReal

noncomputable section

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual total space, with the topology inherited from parameter and
operator norm. -/
abbrev ExactSectionSpace (S : Set E) (K : Set F) (H : P → Submodule ℝ F) :=
  {t : P × (E →L[ℝ] F) // Function.Injective t.2 ∧
    LinearMap.range t.2.toLinearMap = H t.1 ∧ t.2 '' S = K ∩ (H t.1 : Set F)}

namespace ExactSectionAtlas

variable {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H)

def actualModelEquiv : Z.fiberBundleCore.TotalSpace ≃ ExactSectionSpace S K H where
  toFun v :=
    let A := exactBodyMapTorsorEquiv (Z.exactMap v.proj v.proj (Z.mem_baseSet v.proj)) v.snd
    ⟨(v.proj, A.val), A.property⟩
  invFun t := ⟨t.val.1,
    (exactBodyMapTorsorEquiv (Z.exactMap t.val.1 t.val.1 (Z.mem_baseSet t.val.1))).symm
      ⟨t.val.2, t.property⟩⟩
  left_inv := by
    rintro ⟨a, g⟩
    change TotalSpace.mk a
      ((exactBodyMapTorsorEquiv (Z.exactMap a a (Z.mem_baseSet a))).symm
        (exactBodyMapTorsorEquiv (Z.exactMap a a (Z.mem_baseSet a)) g)) = TotalSpace.mk a g
    rw [Equiv.symm_apply_apply]
  right_inv := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((exactBodyMapTorsorEquiv (Z.exactMap t.val.1 t.val.1 (Z.mem_baseSet t.val.1))).apply_symm_apply
          (⟨t.val.2, t.property⟩ : ExactBodyMap S K (H t.val.1)))

theorem localTriv_forward_operator (i : P) (v : Z.fiberBundleCore.TotalSpace)
    (hi : v.proj ∈ Z.baseSet i) :
    (Z.forward i v.proj).comp
        (((Z.fiberBundleCore.localTriv i v).2).val : E →L[ℝ] E) =
      (Z.actualModelEquiv v).val.2 := by
  apply ContinuousLinearMap.ext
  intro x
  change Z.forward i v.proj
      (((Z.transition v.proj i v.proj).val : E →L[ℝ] E) ((v.snd.val : E →L[ℝ] E) x)) =
    Z.forward v.proj v.proj ((v.snd.val : E →L[ℝ] E) x)
  rw [Z.transition_val v.proj i v.proj ⟨Z.mem_baseSet v.proj, hi⟩]
  exact Z.forward_inverse_apply i v.proj hi _
    (Z.forward_mem_range v.proj v.proj (Z.mem_baseSet v.proj) _)

theorem localTriv_inverse_operator (i : P) (t : ExactSectionSpace S K H)
    (hi : t.val.1 ∈ Z.baseSet i) :
    (((Z.fiberBundleCore.localTriv i (Z.actualModelEquiv.symm t)).2).val : E →L[ℝ] E) =
      (Z.inverse i t.val.1).comp t.val.2 := by
  have hf := Z.localTriv_forward_operator i (Z.actualModelEquiv.symm t) hi
  rw [Equiv.apply_symm_apply] at hf
  apply ContinuousLinearMap.ext
  intro x
  have hh := congrArg (fun T : E →L[ℝ] F => Z.inverse i t.val.1 (T x)) hf
  have hleft := congrArg (fun T : E →L[ℝ] E => T
    ((((Z.fiberBundleCore.localTriv i (Z.actualModelEquiv.symm t)).2).val : E →L[ℝ] E) x))
    (Z.left_inverse i t.val.1 hi)
  exact hleft.symm.trans hh

theorem continuous_actualModelEquiv : Continuous Z.actualModelEquiv := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk Z.fiberBundleCore.continuous_proj
  apply continuous_iff_continuousAt.mpr
  intro v
  let i := v.proj
  have hi : v.proj ∈ Z.baseSet i := Z.mem_baseSet i
  obtain ⟨_, hA⟩ := Z.forward_lipschitz i
  have hAat : ContinuousAt (Z.forward i) v.proj :=
    hA.continuousOn.continuousAt ((Z.isOpen_baseSet i).mem_nhds hi)
  have hProj : ContinuousAt Z.fiberBundleCore.proj v := Z.fiberBundleCore.continuous_proj.continuousAt
  have hAFamily := hAat.comp (f := fun w : Z.fiberBundleCore.TotalSpace => w.proj) hProj
  have hSource : (Z.fiberBundleCore.localTriv i).source ∈ 𝓝 v :=
    (Z.fiberBundleCore.localTriv i).open_source.mem_nhds
      ((Trivialization.mem_source _).mpr hi)
  have hTriv : ContinuousAt (Z.fiberBundleCore.localTriv i) v :=
    (Z.fiberBundleCore.localTriv i).continuousOn.continuousAt hSource
  have hVal : Continuous (fun g : bodyAutomorphismGroup S => (g.val : E →L[ℝ] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hCoord : ContinuousAt
      (fun w : Z.fiberBundleCore.TotalSpace => (Z.fiberBundleCore.localTriv i w).2) v :=
    continuous_snd.continuousAt.comp
      (f := fun w : Z.fiberBundleCore.TotalSpace => Z.fiberBundleCore.localTriv i w) hTriv
  have hG := hVal.continuousAt.comp
    (f := fun w : Z.fiberBundleCore.TotalSpace => (Z.fiberBundleCore.localTriv i w).2) hCoord
  have hLocal : ContinuousAt (fun w : Z.fiberBundleCore.TotalSpace =>
      (Z.forward i w.proj).comp
        (((Z.fiberBundleCore.localTriv i w).2).val : E →L[ℝ] E)) v :=
    (ContinuousLinearMap.compL ℝ E E F).continuous₂.continuousAt.comp (hAFamily.prodMk hG)
  apply hLocal.congr_of_eventuallyEq
  have hNear : ∀ᶠ w : Z.fiberBundleCore.TotalSpace in 𝓝 v, w.proj ∈ Z.baseSet i :=
    hProj.preimage_mem_nhds ((Z.isOpen_baseSet i).mem_nhds hi)
  filter_upwards [hNear] with w hw
  exact (Z.localTriv_forward_operator i w hw).symm

theorem continuous_actualModelEquiv_symm : Continuous Z.actualModelEquiv.symm := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (FiberBundle.continuousAt_totalSpace
    (F := bodyAutomorphismGroup S) (E := Z.fiberBundleCore.Fiber) Z.actualModelEquiv.symm).mpr
  have hProj : Continuous (fun t : ExactSectionSpace S K H => t.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hOp : Continuous (fun t : ExactSectionSpace S K H => t.val.2) :=
    continuous_snd.comp continuous_subtype_val
  refine ⟨hProj.continuousAt, ?_⟩
  let i := t.val.1
  have hi : t.val.1 ∈ Z.baseSet i := Z.mem_baseSet i
  obtain ⟨_, hB⟩ := Z.inverse_lipschitz i
  have hBat : ContinuousAt (Z.inverse i) t.val.1 :=
    hB.continuousOn.continuousAt ((Z.isOpen_baseSet i).mem_nhds hi)
  have hBFamily := hBat.comp (f := fun w : ExactSectionSpace S K H => w.val.1) hProj.continuousAt
  have hRaw : ContinuousAt (fun w : ExactSectionSpace S K H =>
      (Z.inverse i w.val.1).comp w.val.2) t :=
    (ContinuousLinearMap.compL ℝ E F E).continuous₂.continuousAt.comp
      (hBFamily.prodMk hOp.continuousAt)
  have hEmb : Topology.IsEmbedding
      (fun g : bodyAutomorphismGroup S => (g.val : E →L[ℝ] E)) :=
    Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  apply hEmb.continuousAt_iff.mpr
  apply hRaw.congr_of_eventuallyEq
  have hNear : ∀ᶠ w : ExactSectionSpace S K H in 𝓝 t, w.val.1 ∈ Z.baseSet i :=
    hProj.continuousAt.preimage_mem_nhds ((Z.isOpen_baseSet i).mem_nhds hi)
  filter_upwards [hNear] with w hw
  exact Z.localTriv_inverse_operator i w hw

/-- The natural operator-subspace topology is the actual bundle topology. -/
def actualHomeomorph : Z.fiberBundleCore.TotalSpace ≃ₜ ExactSectionSpace S K H where
  toEquiv := Z.actualModelEquiv
  continuous_toFun := Z.continuous_actualModelEquiv
  continuous_invFun := Z.continuous_actualModelEquiv_symm

/-- Genuine local trivializations of the actual operator-space projection. -/
def actualTrivialization (i : P) :
    Trivialization (bodyAutomorphismGroup S) (fun t : ExactSectionSpace S K H => t.val.1) :=
  (Z.fiberBundleCore.localTriv i).compHomeomorph Z.actualHomeomorph.symm

@[simp] theorem actualTrivialization_baseSet (i : P) :
    (Z.actualTrivialization i).baseSet = Z.baseSet i := rfl

end ExactSectionAtlas

end
end BanachIsometric
