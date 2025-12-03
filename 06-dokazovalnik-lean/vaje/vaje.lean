-- Strukture:

-- (A x B) ^ C <=> A ^ C x B ^ C
def eksponent (A B C : Type) (f : C → Prod A B) : Prod (C → A) (C → B) :=
  ⟨
    (fun x : C => (f x).1),
    (fun y : C => (f y).2)
  ⟩
def eksponent_prop (A B C : Prop) (f : C → A ∧ B) : (C → A) ∧ (C → B) :=
  ⟨
    (fun (x : C) => (f x).1),
    (fun (y : C) => (f y).2)
  ⟩

def eksponent_prop_s_taktikami (A B C : Prop) (f : C → A ∧ B) : (C → A) ∧ (C → B) :=
  by
    constructor
    · intro h
      apply And.left
      apply f
      exact h
    · intro h
      exact (f h).right






-- ------------------------------
-- Logika

theorem eq1 {A B : Prop} : (A ∧ B) ↔ (B ∧ A) := by
  apply Iff.intro
  · intro h
    symm
    exact h
  · intro h
    symm
    exact h



theorem eq2 {A B : Prop} : (A ∨ B) ↔ (B ∨ A) :=
  by
  apply Iff.intro
  · intro h
    symm
    exact h
  · intro h
    symm
    exact h


theorem eq3 {A B C : Prop} : (A ∧ (B ∧ C)) ↔ (B ∧ (A ∧ C)) :=
  Iff.intro
  (fun h => ⟨ h.2.1 , ⟨h.1, h.2.2⟩ ⟩)
  (fun h => ⟨ h.2.1 , ⟨h.1, h.2.2⟩ ⟩)

theorem eq4 {A B C : Prop} : (A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C)) :=
  by
  apply Iff.intro
  intro h
  cases h
  case inl a => exact Or.inr (Or.inl a)
  case inr bc =>
    cases bc
    case inl b => exact Or.inl b
    case inr c => exact Or.inr (Or.inr c)
  intro h
  cases h
  case inl b => exact Or.inr (Or.inl b)
  case inr ac =>
    cases ac
    case inl a => exact Or.inl a
    case inr c => exact Or.inr ( Or.inr c)





theorem eq5 {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
  Iff.intro
  (fun h => match h with
    | ⟨ ha, Or.inl hb ⟩ => Or.inl ⟨ ha, hb ⟩
    | ⟨ ha, Or.inr hc⟩ => Or.inr ⟨ ha, hc ⟩
  )
  (fun h => match h with
    | Or.inl ⟨ha ,hb⟩ => ⟨ ha, Or.inl hb ⟩
    | Or.inr ⟨ ha, hc ⟩ => ⟨ ha, Or.inr hc⟩

  )

theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) :=
  by
  apply Iff.intro
  · intro h
    constructor
    · intro hb
      apply h
      left
      assumption
    · intro hc
      apply h
      right
      assumption
  · intro h hbc
    cases hbc with
    | inl hb => exact h.left hb
    | inr hc => exact h.right hc






theorem eq7 {A B C : Prop} : C → (A ∧ B) ↔ (C → A) ∧ (C → B) :=
  by
  apply Iff.intro
  · intro h
    constructor
    · intro c
      exact (h c).1
    · intro c
      exact (h c).2
  · intro h c
    constructor
    exact h.1 c
    exact h.2 c




-- ------------------------------
-- Enakosti naravnih števil (z uporabo `calc`)

theorem kvadrat_dvoclenika {a b : Nat} : (a + b)^2 = a^2 + 2 * a * b + b^2 :=
  by
    calc
      (a + b)^2
      _= ( a + b ) * ( a + b) := by rw [Nat.pow_two]
      _= a * (a + b) + b*( a + b) := by rw [Nat.add_mul]
      _= a * a + a * b + b *(a +b) := by rw [Nat.mul_add]
      _= a * a + a* b + (b* a + b* b) := by rw [Nat.mul_add]
      _= a^2 + a * b + (b*a + b^2):= by repeat rw [Nat.pow_two]
      _= a^2 + a * b + ( a*b + b^2) := by rw [Nat.mul_comm b a]
      _= a^2 + a * b +  a * b + b^2 := by repeat rw[Nat.add_assoc]
      _= a^2 + (a * b +  a * b) + b^2 := by rw[Nat.add_assoc (a^2) (a*b) (a*b)]
      _= a^2 + 2* (a * b) + b^2 := by rw[<- Nat.two_mul (a*b)]
      _= a^2 + 2* a * b + b^2 := by rw[Nat.mul_assoc 2 a b]



theorem vsota_eksponent_produkta {a b c d : Nat} : (a * b)^(c + d) = (a^c)*(a^d)*(b^c)*(b^d) :=
  by
    calc
      (a * b)^(c + d)
      _= ((a *b)^c) *((a*b)^d) := by rw[Nat.pow_add]
      _= (a^c * b^c) * (a^d * b^d):= by repeat rw[Nat.mul_pow]
      _= a^c * b^c * a^d * b^d := by repeat rw [Nat.mul_assoc]
      _= a^c * (b^c * a^d) * b^d := by rw[Nat.mul_assoc (a^c)]
      _= a^c * (a^d * b^c )  * b^d := by rw[Nat.mul_comm (a^d)]
      _ = a^c * a^d * b^c * b^d := by repeat rw [Nat.mul_assoc]
