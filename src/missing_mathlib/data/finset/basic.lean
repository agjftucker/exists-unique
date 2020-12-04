import data.finset.basic

open multiset subtype nat

variables {α : Type*} {β : Type*} {γ : Type*}

namespace finset

protected theorem induction' {α : Type*} {p : finset α → Prop}
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α} (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
| ⟨s, nd⟩ := multiset.induction_on s (λ _, h₁) (λ a s IH nd, begin
    cases nodup_cons.1 nd with m nd',
    rw [← (eq_of_veq _ : cons a (finset.mk s _) m = ⟨a ::ₘ s, nd⟩)],
    { exact h₂ (by exact m) (IH nd') },
    { rw [cons_val] }
  end) nd

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