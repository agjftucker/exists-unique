import order.bounded_lattice

universes u v
variables {α : Type u} {β : Type v}

section order_bot
variables [order_bot α] {a b : α}

theorem unique_minimal_of_least (h : ∀ b, ¬ b < a) : a = ⊥ :=
begin
  cases lt_or_eq_of_le (bot_le : ⊥ ≤ a) with hlt he,
  { exfalso,
    exact h ⊥ hlt, },
  { rw he, },
end

end order_bot

section order_top
variables [order_top α] {a b : α}

theorem unique_maximal_of_greatest (h : ∀ b, ¬ a < b) : a = ⊤ :=
begin
  cases lt_or_eq_of_le (le_top : a ≤ ⊤) with hlt he,
  { exfalso,
    exact h ⊤ hlt, },
  { rw he, },
end

end order_top

namespace with_bot

instance [partial_order α] [is_total α (≤)] : is_total (with_bot α) (≤) :=
{ total := fun a b,
  match a, b with
  | none  , _      := or.inl bot_le
  | _     , none   := or.inr bot_le
  | some x, some y := by simp [total_of]
  end }

@[simp] lemma coe_sup_eq_sup_coe [semilattice_sup α] (a b : α) :
  ((a ⊔ b : α) : with_bot α) = (a : with_bot α) ⊔ (b : with_bot α) :=
rfl

end with_bot

namespace with_top

instance [partial_order α] [is_total α (≤)] : is_total (with_top α) (≤) :=
{ total := fun a b,
  match a, b with
  | none  , _      := or.inr le_top
  | _     , none   := or.inl le_top
  | some x, some y := by simp [total_of]
  end }

@[simp] lemma coe_inf_eq_inf_coe [semilattice_inf α] (a b : α) :
  ((a ⊓ b : α) : with_top α) = (a : with_top α) ⊓ (b : with_top α) :=
rfl

end with_top
