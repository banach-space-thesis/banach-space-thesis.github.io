import ThesisCommon.Analysis.FreeNatUltrafilterTopology

/-! Every infinite basic clopen in the free-ultrafilter model of ω* is
an actual homeomorphic copy, via pushforward and pullback of ultrafilters. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon.FreeNatUltrafilter

def push (e : ℕ ↪ ℕ) (U : FreeNatUltrafilter) : FreeNatUltrafilter :=
  ⟨U.val.map e, (Filter.map_mono U.property).trans e.injective.tendsto_cofinite⟩

@[simp] theorem mem_push (e : ℕ ↪ ℕ) (U : FreeNatUltrafilter) (A : Set ℕ) :
    A ∈ push e U ↔ e ⁻¹' A ∈ U := Iff.rfl

theorem continuous_push (e : ℕ ↪ ℕ) : Continuous (push e) := by
  apply Continuous.subtype_mk
  apply ultrafilterBasis_is_basis.continuous_iff.mpr
  rintro _ ⟨A, rfl⟩
  exact (isClopen_basic (e ⁻¹' A)).isOpen

def pull (e : ℕ ↪ ℕ) (U : basic (range e)) : FreeNatUltrafilter :=
  ⟨U.val.val.comap e.injective U.property,
    (Filter.comap_mono U.val.property).trans (Filter.comap_cofinite_le e)⟩

@[simp] theorem mem_pull (e : ℕ ↪ ℕ) (U : basic (range e)) (A : Set ℕ) :
    A ∈ pull e U ↔ e '' A ∈ U.val :=
  U.val.val.mem_comap e.injective U.property

theorem continuous_pull (e : ℕ ↪ ℕ) : Continuous (pull e) := by
  apply Continuous.subtype_mk
  apply ultrafilterBasis_is_basis.continuous_iff.mpr
  rintro _ ⟨A, rfl⟩
  have he : (fun U : basic (range e) => (pull e U).val) ⁻¹'
      {V : Ultrafilter ℕ | A ∈ V} =
      Subtype.val ⁻¹' basic (e '' A) := by
    ext U
    exact mem_pull e U A
  change IsOpen ((fun U : basic (range e) => (pull e U).val) ⁻¹'
    {V : Ultrafilter ℕ | A ∈ V})
  rw [he]
  exact (isClopen_basic (e '' A)).isOpen.preimage continuous_subtype_val

theorem range_mem_push (e : ℕ ↪ ℕ) (U : FreeNatUltrafilter) : range e ∈ push e U := by
  change e ⁻¹' range e ∈ (U.val : Filter ℕ)
  have h : e ⁻¹' range e = univ := by ext n; simp
  rw [h]
  exact Filter.univ_mem

def basicHomeomorph (e : ℕ ↪ ℕ) : FreeNatUltrafilter ≃ₜ basic (range e) where
  toFun U := ⟨push e U, range_mem_push e U⟩
  invFun := pull e
  left_inv U := by
    apply Subtype.ext
    apply Ultrafilter.coe_injective
    exact Filter.comap_map e.injective
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    apply Ultrafilter.coe_injective
    exact Filter.map_comap_of_mem U.property
  continuous_toFun := (continuous_push e).subtype_mk _
  continuous_invFun := continuous_pull e

theorem exists_basic_homeomorph {A : Set ℕ} (hA : A.Infinite) :
    Nonempty (FreeNatUltrafilter ≃ₜ basic A) := by
  letI : Infinite A := hA.to_subtype
  letI := Classical.decPred (fun n => n ∈ A)
  letI : Denumerable A := Classical.choice (nonempty_denumerable A)
  let e : ℕ ≃ A := (Denumerable.eqv A).symm
  let f : ℕ ↪ ℕ := e.toEmbedding.trans (Function.Embedding.subtype A)
  have hf : range f = A := by
    ext n
    constructor
    · rintro ⟨m, rfl⟩
      exact (e m).property
    · intro hn
      exact ⟨e.symm ⟨n, hn⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  exact ⟨hf ▸ basicHomeomorph f⟩

end ThesisCommon.FreeNatUltrafilter
