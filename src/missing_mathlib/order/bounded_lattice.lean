import order.bounded_lattice

universes u v
variables {α : Type u} {β : Type v}

namespace with_bot

@[simp] lemma sup_coe_eq [semilattice_sup α] (a b : α) : ((a ⊔ b : α) : with_bot α) = a ⊔ b :=
rfl

end with_bot