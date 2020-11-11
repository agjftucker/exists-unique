import data.multiset.lattice

variables {α : Type*}

namespace multiset

section sup
variables [semilattice_sup_bot α]

lemma of_sup_of_forall (p : α → Prop) (h0 : p ⊥) (ih : ∀ a b : α, p a → p b → p (a ⊔ b)) :
  ∀ (s : multiset α), (∀ x ∈ s, p x) → p (sup s) :=
@multiset.induction α (λ s, (∀ x ∈ s, p x) → p (sup s)) (λ _, h0)
(λ y t ht hc, (sup_cons y t).symm ▸
  ih y (sup t) (hc y (mem_cons_self y t)) (ht (λ x h, hc x (mem_cons_of_mem h))))

end sup

end multiset