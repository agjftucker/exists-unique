import data.finset.powerset
import missing_mathlib.data.finset.basic

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

variables {p : finset α → Prop}

def decidable_exists_of_ssubsets {s : finset α} :
  (∀ t ⊂ s, decidable (p t)) → decidable (∃ t ⊂ s, p t) :=
begin
  intro h,
  suffices : decidable (∃ t (h₁ : t ∈ s.powerset) (h₂ : ¬ s ⊆ t), p t),
  { apply decidable_of_decidable_of_iff this,
    split,
    { rintros ⟨t, h₁, h₂, h₃⟩,
      use [t, ⟨mem_powerset.1 h₁, h₂⟩, h₃], },
    { rintros ⟨t, ⟨h₁, h₂⟩, h₃⟩,
      use [t, mem_powerset.2 h₁, h₂, h₃], }, },
  apply @finset.decidable_dexists_finset _ _ _ _,
  intros t h₁,
  suffices : ¬ s ⊆ t → decidable (p t),
  { apply @exists_prop_decidable _ _ _ this, },
  intro h₂,
  apply h,
  use [mem_powerset.1 h₁, h₂],
end

end powerset
end finset