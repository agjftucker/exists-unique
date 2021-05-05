import data.finset.powerset

namespace finset
open multiset

variables {α : Type*}

section powerset

variable [decidable_eq α]

def ssubsets (s : finset α) : finset (finset α) :=
erase (powerset s) s

lemma mem_ssubsets_iff {s t : finset α} : t ∈ s.ssubsets ↔ t < s :=
iff.intro
(λ h, lt_of_le_of_ne (mem_powerset.1 (mem_of_mem_erase h)) (ne_of_mem_erase h))
(λ h, mem_erase_of_ne_of_mem (ne_of_lt h) (mem_powerset.2 h.1))

lemma empty_mem_ssubsets {s : finset α} (h : s.nonempty) : ∅ ∈ s.ssubsets :=
mem_ssubsets_iff.2 (lt_of_le_of_ne bot_le (nonempty.ne_empty h).symm)

def decidable_exists_of_ssubsets {s : finset α} {p : ∀ t ⊂ s, Prop}
  (hu : ∀ t (h : t ⊂ s), decidable (p t h)) : decidable (∃ t (h : t ⊂ s), p t h) :=
decidable_of_iff (∃ t (h₁ : t ∈ s.powerset) (h₂ : ¬ s ⊆ t), p t ⟨mem_powerset.1 h₁, h₂⟩)
⟨(λ ⟨t, h₁, h₂, h₃⟩, ⟨t, _, h₃⟩), (λ ⟨t, ⟨h₁, h₂⟩, h₃⟩, ⟨t, mem_powerset.2 h₁, h₂, h₃⟩)⟩

end powerset
end finset