import SurveyStatements.P5L1VariationTreeHaar

/-! Actual finite dyadic symmetries localized inside a chosen dyadic cell.
They fix every terminal cell outside that root. The resulting Reynolds
average is a genuine uniformly bounded operator on interval L¹. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

def localDyadicTreeGroup (M r : ℕ) (hr : r ≤ M) (root : Fin (2 ^ r)) :
    Subgroup (DyadicTreePerm M) where
  carrier := {σ | ∀ a : Fin (2 ^ M), prefixIndex M r hr a ≠ root → σ.val a = a}
  one_mem' := by intro a ha; rfl
  mul_mem' := by
    intro σ τ hσ hτ a ha
    change σ.val (τ.val a) = a
    rw [hτ a ha, hσ a ha]
  inv_mem' := by
    intro σ hσ a ha
    change σ.val.symm a = a
    have h := congrArg σ.val.symm (hσ a ha)
    simpa using h.symm

abbrev LocalDyadicTreePerm (M r : ℕ) (hr : r ≤ M) (root : Fin (2 ^ r)) :=
  localDyadicTreeGroup M r hr root

instance localDyadicTreePermFintype (M r : ℕ) (hr : r ≤ M) (root : Fin (2 ^ r)) :
    Fintype (LocalDyadicTreePerm M r hr root) := Fintype.ofFinite _

def localDyadicTreeLeafAction (M r : ℕ) (hr : r ≤ M) (root : Fin (2 ^ r)) :
    LocalDyadicTreePerm M r hr root →* Equiv.Perm (Fin (2 ^ M)) :=
  (dyadicTreeLeafAction M).comp (localDyadicTreeGroup M r hr root).subtype

theorem localDyadicTreeLeafAction_fixes_outside (M r : ℕ) (hr : r ≤ M)
    (root : Fin (2 ^ r)) (σ : LocalDyadicTreePerm M r hr root)
    (a : Fin (2 ^ M)) (ha : prefixIndex M r hr a ≠ root) :
    localDyadicTreeLeafAction M r hr root σ a = a :=
  σ.property a ha

def localFiniteReynolds (𝕜 : Type*) [RCLike 𝕜]
    (M r : ℕ) (hr : r ≤ M) (root : Fin (2 ^ r))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 :=
  terminalReynolds M (localDyadicTreeLeafAction M r hr root) (extendMeanZero 𝕜 R)

theorem localFiniteReynolds_norm_le (𝕜 : Type*) [RCLike 𝕜]
    (M r : ℕ) (hr : r ≤ M) (root : Fin (2 ^ r))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :
    ‖localFiniteReynolds 𝕜 M r hr root R‖ ≤ 2 * ‖R‖ :=
  (terminalReynolds_norm_le M (localDyadicTreeLeafAction M r hr root)
    (extendMeanZero 𝕜 R)).trans (extendMeanZero_norm_le 𝕜 R)

theorem prefixLift_prefix (M n r : ℕ) (hn : n ≤ M) (hr : r ≤ n)
    (a : Fin (2 ^ n)) :
    prefixIndex M r (hr.trans hn) (prefixLift M n hn a) =
      prefixIndex n r hr a := by
  apply Fin.ext
  change (prefixLift M n hn a).val / 2 ^ (M - r) = a.val / 2 ^ (n - r)
  rw [← prefix_div_comp M n r (prefixLift M n hn a).val hn hr]
  have hl := congrArg Fin.val (prefixIndex_lift M n hn a)
  change (prefixLift M n hn a).val / 2 ^ (M - n) = a.val at hl
  rw [hl]

theorem prefixIndex_comp (M n r : ℕ) (hn : n ≤ M) (hr : r ≤ n)
    (a : Fin (2 ^ M)) :
    prefixIndex n r hr (prefixIndex M n hn a) = prefixIndex M r (hr.trans hn) a := by
  apply Fin.ext
  exact prefix_div_comp M n r a.val hn hr

theorem nodeAction_prefix_comp {M : ℕ} (σ : DyadicTreePerm M)
    (n r : ℕ) (hn : n ≤ M) (hr : r ≤ n) (a : Fin (2 ^ n)) :
    prefixIndex n r hr (nodeAction σ n hn a) =
      nodeAction σ r (hr.trans hn) (prefixIndex n r hr a) := by
  calc
    _ = prefixIndex M r (hr.trans hn) (σ.val (prefixLift M n hn a)) :=
      prefixIndex_comp M n r hn hr _
    _ = nodeAction σ r (hr.trans hn)
        (prefixIndex M r (hr.trans hn) (prefixLift M n hn a)) :=
      nodeAction_prefix σ r (hr.trans hn) _
    _ = _ := by rw [prefixLift_prefix]

theorem localNodeAction_root_fixed (M r : ℕ) (hr : r ≤ M) (root : Fin (2 ^ r))
    (σ : LocalDyadicTreePerm M r hr root) : nodeAction σ.val r hr root = root := by
  have hfix (a : Fin (2 ^ r)) (ha : a ≠ root) : nodeAction σ.val r hr a = a := by
    have hx : prefixIndex M r hr (prefixLift M r hr a) ≠ root := by
      rwa [prefixIndex_lift]
    have h := σ.property (prefixLift M r hr a) hx
    change prefixIndex M r hr (σ.val.val (prefixLift M r hr a)) = a
    rw [h]
    exact prefixIndex_lift M r hr a
  by_contra hne
  let a := nodeAction σ.val r hr root
  have ha : a ≠ root := hne
  have heq : nodeAction σ.val r hr root = nodeAction σ.val r hr a := by rw [hfix a ha]
  exact ha ((nodeAction_injective σ.val r hr) heq).symm

theorem localNodeAction_preserves_root (M n r : ℕ) (hn : n ≤ M) (hr : r ≤ n)
    (root : Fin (2 ^ r)) (σ : LocalDyadicTreePerm M r (hr.trans hn) root)
    (a : Fin (2 ^ n)) :
    prefixIndex n r hr (nodeAction σ.val n hn a) = root ↔ prefixIndex n r hr a = root := by
  rw [nodeAction_prefix_comp]
  constructor
  · intro h
    exact (nodeAction_injective σ.val r (hr.trans hn))
      (h.trans (localNodeAction_root_fixed M r (hr.trans hn) root σ).symm)
  · intro h
    rw [h]
    exact localNodeAction_root_fixed M r (hr.trans hn) root σ

theorem localDyadicTree_transitive (M n r : ℕ) (hn : n ≤ M) (hr : r ≤ n)
    (root : Fin (2 ^ r)) (a b : Fin (2 ^ n))
    (ha : prefixIndex n r hr a = root) (hb : prefixIndex n r hr b = root) :
    ∃ σ : LocalDyadicTreePerm M r (hr.trans hn) root,
      nodeAction σ.val n hn a = b := by
  let x := prefixLift M n hn a
  let y := prefixLift M n hn b
  let mask : Fin (2 ^ M) := ⟨x.val ^^^ y.val, Nat.xor_lt_two_pow x.isLt y.isLt⟩
  have hx : x.val / 2 ^ (M - r) = root.val := by
    exact congrArg Fin.val ((prefixLift_prefix M n r hn hr a).trans ha)
  have hy : y.val / 2 ^ (M - r) = root.val := by
    exact congrArg Fin.val ((prefixLift_prefix M n r hn hr b).trans hb)
  have hmask : mask.val < 2 ^ (M - r) := by
    apply (Nat.div_eq_zero_iff_lt (by positivity)).mp
    change (x.val ^^^ y.val) / 2 ^ (M - r) = 0
    rw [Nat.xor_div_two_pow, hx, hy, Nat.xor_self]
  let σ := localXorTreePermutation M r (hr.trans hn) root mask hmask
  have hlocal : σ ∈ localDyadicTreeGroup M r (hr.trans hn) root := by
    intro z hz
    change localXorLeaf M r root mask z = z
    have hz' : z.val / 2 ^ (M - r) ≠ root.val := fun h => hz (Fin.ext h)
    simp only [localXorLeaf, if_neg hz']
  refine ⟨⟨σ, hlocal⟩, ?_⟩
  have hxy : σ.val x = y := by
    apply Fin.ext
    change (localXorLeaf M r root mask x).val = y.val
    simp only [localXorLeaf, if_pos hx]
    change x.val ^^^ (x.val ^^^ y.val) = y.val
    rw [← Nat.xor_assoc]
    simp
  change prefixIndex M n hn (σ.val x) = b
  rw [hxy]
  exact prefixIndex_lift M n hn b

end SurveyStatements.P5L1Variation

