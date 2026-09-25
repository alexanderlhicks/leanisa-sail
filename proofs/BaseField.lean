import F1eOrderField
import RootOrderExact

namespace Leanisa.Proofs.Quotient

/-- The base quotient is a field, by its accepted cardinality and exact root order. -/
theorem base_isField : IsField KRing :=
  F1eResearch.base_field_if_exact_order root_order_exact

end Leanisa.Proofs.Quotient
