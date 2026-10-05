import Posets.OrdinalIdealTransportBelowSquare
import Posets.CZeroInfiniteFactorization

/-! The scalar theorem discharges the last input for repeated regular
ordinal blocks of smaller cardinality, giving exact Proposition 3.1
throughout κ ≤ α < κ². -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000

theorem smallRepeatedRegularOrdinal_hasUPFP
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    {I : Type} [Infinite I] (hI : Cardinal.mk I < c) :
    HasUPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) :=
  smallRepeatedRegularOrdinal_hasUPFP_of_scalar hc hu hI
    (jlmsScalarCZero_infinite_hasUPFP I)

theorem initialOrdinalInfiniteQuotient_hasUPFP
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{0}} (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α < c.ord * c.ord) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 α) := by
  letI := initialOrdinalInfiniteQuotient_index_infinite hu hlo
  exact initialOrdinalInfiniteQuotient_hasUPFP_of_scalar hc hu hlo hhi
    (jlmsScalarCZero_infinite_hasUPFP _)

theorem proposition_3_1_regular_belowSquare
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{0}} (hlo : c.ord ≤ α) (hhi : α < c.ord * c.ord) :
    Proposition_3_1 𝕜 α :=
  proposition_3_1_regular_belowSquare_of_scalar hc hu
    (fun I hI _ => by letI := hI; exact jlmsScalarCZero_infinite_hasUPFP I) hlo hhi

end Posets
