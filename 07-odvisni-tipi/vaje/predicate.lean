
variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

<<<<<<< HEAD
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  by
  apply Iff.intro
  intro hp x px
  sorry


example : (r → ∀ x, p x) ↔ (∀ x, r → p x) :=
=======
theorem eq1 : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  sorry

theorem eq2 : (r → ∀ x, p x) ↔ (∀ x, r → p x) :=
>>>>>>> 09911a55c1832cc00b5ddb0fb62069d1fba55415
  sorry

theorem eq3 : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) := by
  sorry

theorem eq4 : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) :=
  sorry

-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical
#check Classical.byContradiction
#check Classical.em

theorem eq5 : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
 sorry

theorem eq6 : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) :=
  sorry
