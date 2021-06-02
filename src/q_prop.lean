import q_def

local prefix `𝒫`:100 := λ {α : Type} (s : finset α), {t // t ≤ s}

section
variables {α : Type*} [semilattice_sup_bot α]

/-- To derive our conclusions about `q r` we require of relation `r` certain abstract properties.
Let `r b` denote the set comprising those elements `c` for which `r b c`. Then `r` is a
`support_rel` if each `r b` forms a `semilattice_sup_bot` and if `r` is nondecreasing, i.e. `d ≤ c`
implies `r d ⊆ r c`. -/
class support_rel {α β} [preorder α] [semilattice_sup_bot β] (r : α → β → Prop) : Prop :=
(bottom : ∀ (b : α), r b ⊥)
(sup : ∀ (b c : β) (d : α), r d b → r d c → r d (b ⊔ c))
(mono : ∀ (c d : α), d ≤ c → ∀ (b : β), r d b → r c b)

variables {r : α → α → Prop} [ht : support_rel r]
include ht

lemma r_self_of_q {b : α} : q r b → r b b :=
begin
  intro hqb,
  cases hqb with _ c hlt hr hqc,
  { exact support_rel.bottom ⊥, },
  { exact support_rel.mono b c (le_of_lt hlt) b hr, },
end

lemma r_joins_of_q {b c d : α} : r d c → q r b → r (b ⊔ d) (b ⊔ c) :=
begin
  intros hr hq,
  apply support_rel.sup,
  { exact support_rel.mono (b ⊔ d) b le_sup_left b (r_self_of_q hq), },
  { exact support_rel.mono (b ⊔ d) d le_sup_right c hr, },
end

lemma q_sup_of_foreach {b c : α} : q r b → q r c → q r (b ⊔ c) :=
begin
  intros hb hc,
  induction hc with d e hed hr hq hq',
  { rwa sup_bot_eq, },
  { cases lt_or_eq_of_le (sup_le_sup_left (le_of_lt hed) b) with hlt he,
    { exact q.succ hlt (r_joins_of_q hr hb) hq', },
    { rwa he at hq', }, },
end

lemma q_sup_of_forall (s : finset α) : (∀ b ∈ s, q r b) → q r (s.sup id) :=
begin
  apply finset.sup_induction,
  apply q.base,
  apply q_sup_of_foreach,
end

lemma exists_ge_term_of_q {a : α} :
  q r a → ∀ c < a, q r c → ∃ b, c ≤ b ∧ b < a ∧ q r b ∧ r b a :=
begin
  suffices : ∀ d ≤ a, q r d → ∀ c < a, q r c → ∃ b, c ≤ b ∧ b < a ∧ q r b ∧ r b (c ⊔ d),
  { intros hqa c hca hqc,
    specialize this a (le_refl a) hqa c hca hqc,
    rwa sup_of_le_right (le_of_lt hca) at this, },
  intros d hle hqd c hca hqc,
  induction hqd with e f hfe hr hqf h₄ h₅,
  { rw sup_bot_eq,
    use [c, le_refl c, hca, hqc, r_self_of_q hqc], },
  { have hfa := le_trans (le_of_lt hfe) hle,
    cases lt_or_eq_of_le (sup_le (le_of_lt hca) hfa) with hlt he,
    { use [c ⊔ f, le_sup_left, hlt, q_sup_of_foreach hqc hqf],
      apply r_joins_of_q hr hqc, },
    { rcases h₄ hfa with ⟨b, hb₁, hb₂, hb₃, hb₄⟩,
      use [b, hb₁, hb₂, hb₃],
      suffices : c ⊔ f = c ⊔ e,
      { rwa this at hb₄, },
      apply le_antisymm,
      { exact sup_le_sup_left (le_of_lt hfe) c, },
      { rw he,
        exact sup_le (le_of_lt hca) hle, }, }, },
end

end

namespace si
variables {β : Type} [decidable_eq β] {A : finset β}

variables {r : 𝒫 A → 𝒫 A → Prop} [decidable_rel r] [ht : support_rel r]
include ht

lemma q_φ : q r (si.φ r) :=
begin
  apply q_sup_of_forall,
  intros B hB,
  rw finset.mem_filter at hB,
  exact hB.2,
end

end si
