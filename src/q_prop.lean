import q_def

local prefix `𝒫`:100 := λ {α : Type} (s : finset α), {t // t ≤ s}

section
variables {α : Type*} [bounded_join_semilattice α] {r : α → α → Prop}

variable hr₁ (b c d : α) : c < ⊤ → d ≤ c → r d b → r c b
variable hr₂ (b c d : α) : r d b → r d c → r d (b ⊔ c)

include hr₁

lemma hr₄ {b : α} : ⊥ < b → b < ⊤ → q r b → r b b :=
begin
  intros hb ht hq,
  rcases hq with _ | ⟨_, c, hlt, hr, hq⟩,
  { exfalso,
    exact not_lt_bot hb, },
  { exact hr₁ _ _ _ ht (le_of_lt hlt) hr, },
end

include hr₂

lemma hr₅ {b c d : α} : b ⊔ d < ⊤ → r d c → q r b → r (b ⊔ d) (b ⊔ c) :=
begin
  intros ht hr hq,
  cases lt_or_eq_of_le (order_bot.bot_le b) with hb hb,
  { apply hr₂,
    { apply hr₁ _ _ _ ht le_sup_left,
      refine hr₄ hr₁ hb _ hq,
      exact lt_of_le_of_lt le_sup_left ht, },
    { exact hr₁ _ _ _ ht le_sup_right hr, }, },
  { rw [← hb, bot_sup_eq, bot_sup_eq],
    exact hr, },
end

lemma q_of_sup_of_foreach : ∀ b c, q r b → q r c → q r (b ⊔ c) :=
begin
  rintros b c hb hc,
  apply hc.rec_on,
  { convert hb,
    exact sup_bot_eq, },
  { intros c d hd hr hq,
    cases lt_or_eq_of_le (sup_le_sup_left (le_of_lt hd) b) with hlt he,
    { apply q.succ hlt,
      exact hr₅ hr₁ hr₂ (lt_of_lt_of_le hlt le_top) hr hb, },
    { intro h,
      rwa ←he, }, },
end

lemma q_of_sup_of_forall (s : finset α) : (∀ b ∈ s, q r b) → q r (s.sup id) :=
begin
  apply finset.of_sup_of_forall,
  apply q.base,
  apply q_of_sup_of_foreach hr₁ hr₂,
end

end

namespace si

variables {β : Type} [decidable_eq β]
variables {A : finset β} {r : 𝒫 A → 𝒫 A → Prop} [decidable_rel r]

variable hr₁ (B C D : 𝒫 A) : C < ⊤ → D ≤ C → r D B → r C B
variable hr₂ (B C D : 𝒫 A) : r D B → r D C → r D (B ⊔ C)

include hr₁ hr₂

lemma q_φ : q r (si.φ r) :=
begin
  apply q_of_sup_of_forall hr₁ hr₂,
  intros B hB,
  rw finset.mem_filter at hB,
  exact hB.2,
end

end si