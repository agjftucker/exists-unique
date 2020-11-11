import finset.powerset
import finset.lattice

local prefix `𝒫`:100 := λ {α : Type} (s : finset α), {t // t ∈ s.powerset}

section
variables {α : Type*} [semilattice_sup_bot α] (r : α → α → Prop)

inductive q : α → Prop
| base : q ⊥
| succ {b c : α} : c < b → r c b → q c → q b

end

section
variables {α : Type*} [bounded_lattice α] {r : α → α → Prop}

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
  intro h,
  apply finset.of_sup_of_forall,
  apply q.base,
  apply q_of_sup_of_foreach hr₁ hr₂,
  exact h,
end

end

section     --should be in finset.basic? section decidable_eq
open finset
variables {β : Type} [decidable_eq β] {A : finset β}

instance lattice_of_bdd_above_finset : lattice (𝒫 A) :=
begin
  apply subtype.lattice,
  { simp_rw mem_powerset,
    intros B C,
    exact union_subset, },
  { simp_rw mem_powerset,
    intros B C hB,
    apply subset.trans,
    apply inter_subset_right, },
end

instance bdd_lattice_of_bdd_above_finset : bounded_lattice (𝒫 A) :=
{ bot := ⟨∅, empty_mem_powerset A⟩,
  bot_le := λ ⟨B, hB⟩, empty_subset B,
  top := ⟨A, mem_powerset_self A⟩,
  le_top := λ ⟨B, hB⟩, mem_powerset.1 hB,
  ..lattice_of_bdd_above_finset }

lemma strong_induction' {p : 𝒫 A → Sort*} : (∀ C, (∀ D, D < C → p D) → p C) → (∀ B, p B) :=
begin
  rintros ih ⟨B, hB⟩,
  revert hB,
  apply strong_induction_on B,
  intros C ih' hC,
  apply ih,
  rintros ⟨D, hD⟩ hD',
  exact ih' D hD' hD,
end

end

section

variables {β : Type} [decidable_eq β]
variables {A : finset β} (r : 𝒫 A → 𝒫 A → Prop) [decidable_rel r]

variable [decidable_pred (q r)] --should be able to prove this

def φ : 𝒫 A := (A.powerset.attach.filter (q r)).sup id

variable hr₁ (B C D : 𝒫 A) : C < ⊤ → D ≤ C → r D B → r C B
variable hr₂ (B C D : 𝒫 A) : r D B → r D C → r D (B ⊔ C)

include hr₁ hr₂

example : q r (φ r) :=
begin
  apply q_of_sup_of_forall hr₁ hr₂,
  intros B hB,
  rw finset.mem_filter at hB,
  exact hB.2,
end

end