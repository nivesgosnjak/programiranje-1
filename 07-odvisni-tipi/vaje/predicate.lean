
variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  by
  apply Iff.intro
  intro h x px
  apply h
  exact ⟨ x, px ⟩
  intro h hp
  let ⟨ x, hp ⟩ := hp
  exact h x hp 



example : (r → ∀ x, p x) ↔ (∀ x, r → p x) :=
  by
  apply Iff.intro
  intro h x hr
  exact h hr x
  intro h hr x
  exact h x hr

example : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) := 
  by
  apply Iff.intro
  intro ⟨hr, ⟨ x, hx⟩⟩ 
  apply Exists.intro x ⟨ hr, hx ⟩ 
  intro ⟨ x, ⟨ hr, hp⟩ ⟩ 
  constructor
  exact hr
  exact ⟨ x, hp⟩ 
  



example : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) :=
  by
  intro h x
  cases h
  case inl hr => exact Or.inl hr
  case inr hpx => exact Or.inr (hpx x)

-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  by
  apply Iff.intro
  intro h
  apply Classical.byContradiction
  intro npx
  apply h
  intro x
  apply Classical.byContradiction
  intro px
  apply npx
  exact ⟨ x, px⟩ 
  intro h npx
  let ⟨ x, npx'⟩ := h
  apply npx'
  apply npx 




example : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) :=
  by
  apply Iff.intro
  intro h x
  cases h
  case inl hr => exact Or.inl hr
  case inr hpx => exact Or.inr (hpx x)
  intro h
  have x := Classical.em r
  cases x
  case inl hr => exact Or.inl hr
  case inr nhr =>
    right
    intro x
    have xx := h x
    cases xx
    case inl hr => contradiction
    case inr hp => exact hp
