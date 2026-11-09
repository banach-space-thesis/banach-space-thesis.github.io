import BanachIsometric.FiniteNerveOrderPrismEndpoints

/-! Actual comparable vertex maps used to contract a cone at an arbitrary
apex. The minimum vertex map lies below both the identity and the constant
apex map, and every interpolating tuple stays in the given finite complex. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι]

def coneMinVertex (a : ι) : ι →o ι := ⟨fun x => min a x, fun _ _ h => min_le_min_left a h⟩
def coneIdentityVertex : ι →o ι := ⟨id, monotone_id⟩
def coneConstantVertex (a : ι) : ι →o ι := ⟨fun _ => a, monotone_const⟩

theorem coneMinVertex_le_identity (a : ι) (x : ι) :
    coneMinVertex a x ≤ coneIdentityVertex x := min_le_right _ _

theorem coneMinVertex_le_constant (a : ι) (x : ι) :
    coneMinVertex a x ≤ coneConstantVertex a x := min_le_left _ _

theorem coneMinVertex_mem_insert (a : ι) {s : Finset ι} {x : ι} (hx : x ∈ s) :
    coneMinVertex a x ∈ insert a s := by
  rcases le_total a x with h | h
  · change min a x ∈ insert a s
    rw [min_eq_left h]
    exact Finset.mem_insert_self _ _
  · change min a x ∈ insert a s
    rw [min_eq_right h]
    exact Finset.mem_insert_of_mem hx

variable [Fintype ι]

theorem coneMinIdentity_faces (K : Complex ι) (a : ι)
    (hcone : ∀ s ∈ K.faces, insert a s ∈ K.faces) (s : Finset ι) (hs : s ∈ K.faces) :
    s.image (coneMinVertex a) ∪ s.image coneIdentityVertex ∈ K.faces := by
  apply K.downward _ (hcone s hs) _
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact coneMinVertex_mem_insert a hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_insert_of_mem hy
  · exact (Finset.image_nonempty.mpr (K.nonempty s hs)).mono Finset.subset_union_left

theorem coneMinConstant_faces (K : Complex ι) (a : ι)
    (hcone : ∀ s ∈ K.faces, insert a s ∈ K.faces) (s : Finset ι) (hs : s ∈ K.faces) :
    s.image (coneMinVertex a) ∪ s.image (coneConstantVertex a) ∈ K.faces := by
  apply K.downward _ (hcone s hs) _
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact coneMinVertex_mem_insert a hy
    · obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_insert_self _ _
  · exact (Finset.image_nonempty.mpr (K.nonempty s hs)).mono Finset.subset_union_left

theorem weakVertexChainMap_identity (K : Complex ι)
    (hf : ∀ s ∈ K.faces, s.image coneIdentityVertex ∈ K.faces) (n : ℕ) :
    weakVertexChainMap K coneIdentityVertex hf n = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v c
  rw [weakVertexChainMap_single]
  rfl

theorem strictChainProjection_constant (K : Complex ι) (a : ι)
    (hf : ∀ s ∈ K.faces, s.image (coneConstantVertex a) ∈ K.faces) (n : ℕ) :
    (strictChainProjection K (n + 1)).comp (weakVertexChainMap K (coneConstantVertex a) hf (n + 1)) = 0 := by
  apply Finsupp.lhom_ext
  intro v c
  have hsingle : Finsupp.single v c = c • Finsupp.single v 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.comp_apply, weakVertexChainMap_single, strictChainProjection_single]
  have hnot : ¬ StrictMono (orderedVertexMap K (coneConstantVertex a) hf v).val := by
    intro h
    have h01 : (0 : Fin (n + 2)) < (0 : Fin (n + 1)).succ := by simp
    have he := h h01
    change a < a at he
    exact lt_irrefl a he
  rw [dif_neg hnot]
  rfl

end BanachIsometric.FiniteNerve
