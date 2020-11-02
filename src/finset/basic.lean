import data.finset.basic

open multiset subtype nat

variables {α : Type*} {β : Type*} {γ : Type*}

namespace finset
section card

def strong_induction {p : finset α → Sort*} (ih : ∀s, (∀t ⊂ s, p t) → p s) :
  ∀ (s : finset α), p s
| s := ih s (λ t h, have card t < card s, from card_lt_card h, strong_induction t)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf card⟩]}

theorem strong_induction_eq {p : finset α → Sort*} (H : Π s, (Π t, t ⊂ s → p t) → p s)
  (s : finset α) : strong_induction H s = H s (λ t h, strong_induction H t) :=
by rw strong_induction

end card
end finset