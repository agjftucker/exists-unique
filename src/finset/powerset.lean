import finset.basic
import data.finset.powerset

namespace finset
open multiset

variables {α : Type*}

section powerset

variables (p : finset α → Prop) [decidable_eq α]

def decidable_exists_of_ssubsets (s : finset α) :
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