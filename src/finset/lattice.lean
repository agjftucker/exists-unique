import finset.basic
import data.finset.lattice
import multiset.lattice

variables {α β γ : Type*}

namespace finset

section sup
variables [semilattice_sup_bot α]

lemma of_sup_of_forall {p : α → Prop} (h0 : p ⊥) (ih : ∀ a b : α, p a → p b → p (a ⊔ b)) :
  ∀ (s : finset α), (∀ x ∈ s, p x) → p (s.sup id) :=
begin
  intros s hs,
  rw [sup_def, multiset.map_id],
  exact multiset.of_sup_of_forall p h0 ih s.1 hs,
end

end sup
end finset