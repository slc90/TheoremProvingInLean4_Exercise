section e1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (fun h : ∀ x, p x ∧ q x =>
    have h1 : ∀ x, p x :=
      fun x : α =>
        have h1 := h x
        h1.left
    have h2 : ∀ x, q x :=
      fun x : α =>
        have h1 := h x
        h1.right
    show (∀ x, p x) ∧ (∀ x, q x) from ⟨h1,h2⟩)
  (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
    have h1 := h.left
    have h2 := h.right
    fun x : α =>
      have px := h1 x
      have qx := h2 x
      show p x ∧ q x from ⟨px,qx⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1 : ∀ x, p x → q x =>
    fun h2 : ∀ x, p x =>
      fun x : α =>
        have px_qx := h1 x
        have px := h2 x
        show q x from px_qx px

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    fun x : α =>
      Or.elim h
      (fun h1 : ∀ x, p x =>
        have px := h1 x
        Or.inl px)
      (fun h1 : ∀ x, q x =>
        have qx := h1 x
        Or.inr qx)

end e1

section e2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun x : α =>
    Iff.intro
    (fun h : ∀ x : α, r => h x)
    (fun h : r =>
      fun y : α => h)

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (fun h : ∀ x, p x ∨ r =>
    Or.elim (em r)
    (fun h1 : r => show (∀ x, p x) ∨ r from Or.inr h1)
    (fun h1 : ¬r =>
      have h2 : ∀ x, p x :=
        fun x : α =>
          have y := h x
          Or.elim y
          (fun z : p x => z)
          (fun z : r => absurd z h1)
      show (∀ x, p x) ∨ r from Or.inl h2))
  (fun h : (∀ x, p x) ∨ r =>
    Or.elim h
    (fun h1 : ∀ x, p x =>
      fun x : α =>
        show p x ∨ r from Or.inl (h1 x))
    (fun h1 : r =>
      fun x : α =>
        show p x ∨ r from Or.inr h1))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
  (fun h : ∀ x, r → p x =>
    fun y : r =>
      fun x : α =>
        have h1 : r → p x := h x
        h1 y)
  (fun h : r → ∀ x, p x =>
    fun x : α =>
      fun y : r =>
        have z : ∀x, p x := h y
        z x)

end e2

section e3
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    have h1 := h barber
    have h2 := Iff.mp h1
    have h3 := Iff.mpr h1
    have h4 :=
      fun y : shaves barber barber =>
        have h5 := h2 y
        h5 y
    have h5 := h3 h4
    have h6 := h2 h5
    show False from h6 h5

end e3

section e4
def even (n : Nat) : Prop := ∃b, 2 * b = n

def prime (n : Nat) : Prop :=
  n >= 2 ∧ ∀ m k : Nat, n = m * k → m = 1 ∨ k = 1

def infinitely_many_primes : Prop :=
  ∀ n : Nat, ∃ k , k > n ∧ prime k

def Fermat_prime (n : Nat) : Prop :=
  ∃ k : Nat, n = 2^(2^k) + 1 ∧ prime n

def infinitely_many_Fermat_primes : Prop :=
  ∀ n : Nat, ∃ k , k > n ∧ Fermat_prime k

def goldbach_conjecture : Prop :=
  ∀ n : Nat, n > 2 ∧ even n → ∃ p q , prime p ∧ prime q ∧ n = p + q

def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, n > 5 ∧ ¬ even n → ∃ p q r, prime p ∧ prime q ∧ prime r ∧ n = p + q + r

def Fermat's_last_theorem : Prop :=
  ∀ n x y z : Nat, ¬(n > 2 ∧ x^n + y^n = z^n)

end e4

section e5
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun h : ∃ x : α, r =>
    have ⟨(w : α),(hw : r)⟩ := h
    hw

example (a : α) : r → (∃ x : α, r) :=
  fun h : r =>
    ⟨a,h⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (fun h : ∃ x, p x ∧ r =>
    have ⟨w,hw⟩ := h
    have px := hw.left
    have y : ∃ x, p x := ⟨w,px⟩
    show (∃ x, p x) ∧ r from ⟨y,hw.right⟩)
  (fun h : (∃ x, p x) ∧ r =>
    have y : ∃ x, p x := h.left
    have hr : r := h.right
    have ⟨w,hw⟩ := y
    show ∃ x, p x ∧ r from ⟨w,⟨hw,hr⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (fun h : ∃ x, p x ∨ q x =>
    have ⟨w, hw⟩ := h
    Or.elim hw
    (fun h1 : p w =>
      have y := ⟨w,h1⟩
      Or.inl y)
    (fun h1 : q w =>
      have y := ⟨w,h1⟩
      Or.inr y))
  (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
    Or.elim h
    (fun h1 : ∃ x, p x =>
      have ⟨w,hw⟩ := h1
      have y : p w ∨ q w := Or.inl hw
      ⟨w,y⟩)
    (fun h1 : ∃ x, q x =>
      have ⟨w,hw⟩ := h1
      have y : p w ∨ q w := Or.inr hw
      ⟨w,y⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h : ∀ x, p x =>
    fun h1 : ∃ x, ¬ p x =>
      have ⟨w,hw⟩ := h1
      have pw := h w
      hw pw)
  (fun h : ¬ (∃ x, ¬ p x) =>
    fun x : α =>
      byContradiction
        (fun h1 : ¬ p x =>
          have y : ∃ x, ¬ p x := ⟨x,h1⟩
          show False from h y))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h : ∃ x, p x =>
    fun h1 : ∀ x, ¬ p x =>
      have ⟨w,hpw⟩ := h
      have hnpw := h1 w
      hnpw hpw)
  (fun h : ¬ (∀ x, ¬ p x) =>
    byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x : α =>
          fun h3 : p x =>
            have y : ∃ x, p x := ⟨x,h3⟩
            h1 y
      h h2))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h : ¬ ∃ x, p x =>
    fun x : α =>
      fun h1 : p x =>
        have y : ∃ x, p x := ⟨x,h1⟩
        h y)
  (fun h : ∀ x, ¬ p x =>
    fun h1 : ∃ x, p x =>
      have ⟨w,hpw⟩ := h1
      have hnpw := h w
      hnpw hpw)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h : ¬ ∀ x, p x =>
    byContradiction
    (fun h1 : ¬ ∃ x, ¬ p x =>
      have h2 : ∀ x, p x :=
        fun x : α =>
          byContradiction
          (fun h3 : ¬ p x =>
            have y : ∃ x, ¬ p x := ⟨x,h3⟩
            h1 y)
      h h2))
  (fun h : ∃ x, ¬ p x =>
    fun h1 : ∀ x, p x =>
      have ⟨w,hnpw⟩ := h
      have hpw := h1 w
      hnpw hpw)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
  (fun h : ∀ x, p x → r =>
    fun h1 : ∃ x, p x =>
      have ⟨w,hpw⟩ := h1
      have pwr : p w → r := h w
      pwr hpw)
  (fun h : (∃ x, p x) → r =>
    fun x : α =>
      fun h1 : p x =>
        have px : ∃ x, p x := ⟨x,h1⟩
        h px)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
  (fun h : ∃ x, p x → r =>
    fun h1 : ∀ x, p x =>
      have ⟨w,(hpwr : p w → r)⟩ := h
      have pw := h1 w
      hpwr pw)
  (fun h : (∀ x, p x) → r =>
    byCases
    (fun h1 : ∀ x, p x =>
      have hr : r := h h1
      have hpar : p a → r := fun _ : p a => hr
      ⟨a,hpar⟩)
    (fun hn1 : ¬ ∀ x, p x =>
      byContradiction
      (fun h2 : ¬ ∃ x, p x → r =>
        have h3 : ∀ x, p x :=
          fun x : α =>
            byContradiction
            (fun h4 : ¬ p x =>
              have h5 : ∃ x, p x → r :=
                ⟨x,fun h6 : p x => absurd h6 h4⟩
              h2 h5)
        hn1 h3)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
  (fun h : ∃ x, r → p x =>
    fun hr : r =>
      have ⟨w,(hrpw : r → p w)⟩ := h
      have hpw := hrpw hr
      ⟨w,hpw⟩)
  (fun h : r → ∃ x, p x =>
    Or.elim (em r)
    (fun hr : r =>
      have h1 : ∃ x, p x := h hr
      have ⟨w,hpw⟩ := h1
      show ∃ x, r → p x from ⟨w,fun _ : r => hpw⟩)
    (fun hnr : ¬r =>
      have y : r → p a :=
        fun h2 : r =>
          absurd h2 hnr
      ⟨a,y⟩))

end e5
