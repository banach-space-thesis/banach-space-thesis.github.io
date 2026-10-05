import JLMS.OrdinalSpacePowerSuccessor
import Mathlib.SetTheory.Cardinal.Ordinal

/-! Uniform tools for a bounded multiplicative change of finite ordinal
exponents. The index reparametrizations are actual isometries of c₀ sums. -/

noncomputable section
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance powerDoublingToolsEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerDoublingToolsEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerDoublingToolsSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance powerDoublingToolsSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem paperOrdinalFinitePower_card (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (n : ℕ) (hn : 1 ≤ n) : (c.ord ^ (n : Ordinal)).card = c := by
  rw [Ordinal.card_opow_eq_of_omega0_le_left
    (by simpa using Cardinal.ord_le_ord.mpr hc) (by exact_mod_cast (by omega : 0 < n)),
    Cardinal.card_ord, Ordinal.card_nat]
  exact max_eq_left ((Cardinal.nat_lt_aleph0 n).le.trans hc)

def paperOrdinalFinitePowerIioEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (n : ℕ) (hn : 1 ≤ n) : Set.Iio c.ord ≃ Set.Iio (c.ord ^ (n : Ordinal)) :=
  Classical.choice (Cardinal.eq.mp (by
    rw [Ordinal.mk_Iio_ordinal, Ordinal.mk_Iio_ordinal, Cardinal.card_ord,
      paperOrdinalFinitePower_card c hc n hn]))

theorem paperOrdinalFinitePower_succ_pred (n : ℕ) (hn : 2 ≤ n) :
    Order.succ ((n - 1 : ℕ) : Ordinal.{u}) = (n : Ordinal) := by
  rw [← Ordinal.natCast_succ]
  exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ n))

theorem paperOrdinalFinitePowerReplication_exists (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ e : JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (n : Ordinal)) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : Set.Iio c.ord =>
        JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (n : Ordinal))),
      (∀ x, ‖e x‖ ≤ 64 * ‖x‖) ∧ (∀ y, ‖e.symm y‖ ≤ 64 * ‖y‖) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have he : n = (k + 1) + 1 := by omega
  rw [he, Ordinal.natCast_succ]
  have hβ : (1 : Ordinal.{u}) ≤ ((k + 1 : ℕ) : Ordinal) := by exact_mod_cast (by omega : 1 ≤ k + 1)
  exact ⟨JLMS.ordinalEndpointZeroPowerSuccessorReplication c hc _ hβ,
    JLMS.norm_ordinalEndpointZeroPowerSuccessorReplication_le c hc _ hβ,
    JLMS.norm_ordinalEndpointZeroPowerSuccessorReplication_symm_le c hc _ hβ⟩

def paperOrdinalFinitePowerReplication (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (n : ℕ) (hn : 2 ≤ n) :
    JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (n : Ordinal)) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : Set.Iio c.ord =>
        JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (n : Ordinal))) :=
  Classical.choose (paperOrdinalFinitePowerReplication_exists c hc n hn)

theorem paperOrdinalFinitePowerReplication_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n)
    (x : JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (n : Ordinal))) :
    ‖paperOrdinalFinitePowerReplication c hc n hn x‖ ≤ 64 * ‖x‖ := by
  exact (Classical.choose_spec (paperOrdinalFinitePowerReplication_exists c hc n hn)).1 x

theorem paperOrdinalFinitePowerReplication_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n)
    (x : JLMS.CZeroSum 𝕜 (fun _ : Set.Iio c.ord =>
      JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (n : Ordinal)))) :
    ‖(paperOrdinalFinitePowerReplication c hc n hn).symm x‖ ≤ 64 * ‖x‖ := by
  exact (Classical.choose_spec (paperOrdinalFinitePowerReplication_exists c hc n hn)).2 x

theorem paperOrdinalFinitePower_add (c : Cardinal.{u}) (m n : ℕ) :
    c.ord ^ (((m + 1) * n : ℕ) : Ordinal) =
      c.ord ^ ((m * n : ℕ) : Ordinal) * c.ord ^ (n : Ordinal) := by
  rw [Nat.add_mul, one_mul, Nat.cast_add, Ordinal.opow_add]

theorem paperOrdinalFinitePower_absorption (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (m n : ℕ) (hm : 1 ≤ m) :
    c.ord ^ (n : Ordinal) = c.ord ^ ((m * n : ℕ) : Ordinal) ∨
      c.ord ^ (n : Ordinal) + c.ord ^ ((m * n : ℕ) : Ordinal) =
        c.ord ^ ((m * n : ℕ) : Ordinal) := by
  have hlo : c.ord ^ (n : Ordinal) ≤ c.ord ^ ((m * n : ℕ) : Ordinal) :=
    Ordinal.opow_le_opow_right
      (Ordinal.omega0_pos.trans_le (by simpa using Cardinal.ord_le_ord.mpr hc))
      (by exact_mod_cast Nat.le_mul_of_pos_left n (by omega : 0 < m))
  rcases hlo.eq_or_lt with h | h
  · exact Or.inl h
  · exact Or.inr (Ordinal.principal_add_iff_add_left_eq_self.mp
      (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) _) _ h)

def paperOrdinalFinitePowerStep (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (((m + 1) * n : ℕ) : Ordinal)) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : Set.Iio c.ord =>
        JLMS.ordinalEndpointZero 𝕜 (c.ord ^ ((m * n : ℕ) : Ordinal))) :=
  (JLMS.ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜)
    (paperOrdinalFinitePower_add c m n)).toContinuousLinearEquiv.trans
    ((JLMS.ordinalEndpointZeroMultipleSumEquiv _ _
      (JLMS.ordinalInitialPower_infinite c hc _ (by exact_mod_cast (Nat.mul_le_mul hm hn)))
      (JLMS.ordinalInitialPower_infinite c hc _ (by exact_mod_cast hn))
      (paperOrdinalFinitePower_absorption c hc m n hm)).trans
        (JLMS.CZeroSum.reindex (𝕜 := 𝕜)
          (E := fun _ : Set.Iio (c.ord ^ (n : Ordinal)) =>
            JLMS.ordinalEndpointZero 𝕜 (c.ord ^ ((m * n : ℕ) : Ordinal)))
          (paperOrdinalFinitePowerIioEquiv c hc n hn)).toContinuousLinearEquiv)

theorem paperOrdinalFinitePowerStep_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (x : JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (((m + 1) * n : ℕ) : Ordinal))) :
    ‖paperOrdinalFinitePowerStep c hc m n hm hn x‖ ≤ 8 * ‖x‖ := by
  unfold paperOrdinalFinitePowerStep
  simp only [ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map]
  exact (JLMS.norm_ordinalEndpointZeroMultipleSumEquiv_le _ _ _ _ _ _).trans_eq
    (congrArg (8 * ·) (LinearIsometryEquiv.norm_map _ _))

theorem paperOrdinalFinitePowerStep_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (x : JLMS.CZeroSum 𝕜 (fun _ : Set.Iio c.ord =>
      JLMS.ordinalEndpointZero 𝕜 (c.ord ^ ((m * n : ℕ) : Ordinal)))) :
    ‖(paperOrdinalFinitePowerStep c hc m n hm hn).symm x‖ ≤ 8 * ‖x‖ := by
  unfold paperOrdinalFinitePowerStep
  simp only [ContinuousLinearEquiv.symm_trans_apply,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
  exact (JLMS.norm_ordinalEndpointZeroMultipleSumEquiv_symm_le _ _ _ _ _ _).trans_eq
    (congrArg (8 * ·) (LinearIsometryEquiv.norm_map _ _))

end Posets
