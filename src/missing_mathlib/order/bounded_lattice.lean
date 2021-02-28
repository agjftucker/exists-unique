import order.bounded_lattice

universes u v
variables {α : Type u} {β : Type v}

section order_top
variables [order_top α] {a b : α}

theorem unique_maximal_of_greatest (hy : ∀ b, ¬ a < b) : a = ⊤ :=
begin
  cases lt_or_eq_of_le (le_top : a ≤ ⊤) with hlt he,
  { exfalso,
    exact hy ⊤ hlt, },
  { exact he, },
end

end order_top

namespace with_bot

@[simp] lemma sup_coe_eq [semilattice_sup α] (a b : α) : ((a ⊔ b : α) : with_bot α) = a ⊔ b :=
rfl

end with_bot
