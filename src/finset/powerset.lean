import finset.basic
import data.finset.powerset

namespace finset
open multiset

variables {α : Type*}

section powerset

variables (p : finset α → Prop) [decidable_pred p]

instance decidable_exists_of_subsets (s : finset α) : decidable (∃ t ⊆ s, p t) :=
decidable_of_iff (∃ t (h : t ∈ s.powerset), p t) $ by finish

variable [decidable_eq α]

instance decidable_exists_of_ssubsets (s : finset α) : decidable (∃ t ⊂ s, p t) :=
decidable_of_iff (∃ t (h : t ∈ s.powerset) (h' : ¬ s ⊆ t), p t) $ by finish

end powerset
end finset