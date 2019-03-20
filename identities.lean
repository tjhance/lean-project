import data.nat.choose
import data.set
import data.set.finite
import data.multiset
import data.list

#check set
#check finset ℕ 
#check @finset.mk
#check choose 5 4

/- Collaboration between
   Travis Hance (thance)
   Katherine Cordwell (kcordwell)
-/

/- Our plan is to prove various combinatorial identities.
In paritcular,

 - Vandermonde's identity (Katherine's focus)
 - the Hockeystick identity (Katherine's focus)
 - the catalan identity: that the catalan numbers, as defined
    by the usual recurrence, equals (1/(n+1))*(2n+1 choose n). (Travis's focus)

For some or all of these, we will use combinatorial bijections.
-/

/-
    Machinery for bijective proofs.
    `has_card` is a Prop that indicates a set is finite
    and has a certain cardinality.

    Below are several theorems for using a bijection
    between multiple sets to establish a relation between their
    sizes. (Both Travis and Katherine's focus)
-/

def has_card {α : Type} (s : set α) (n : ℕ) : Prop :=
    ∃ l : (list α) , list.length l = n ∧ (∀ x : α , x ∈ s ↔ x ∈ l)
            ∧ list.nodup l

theorem card_bijection
    {α : Type} {β : Type}
        (A : set α) (B : set β) (a : ℕ)
        (f : (α → β)) :
    (∀ (x:α) , x ∈ A → f x ∈ B) →
    (∀ y , y ∈ B → ∃ x , x ∈ A ∧ f x = y) →
    (∀ x x' , x ∈ A → x' ∈ A → f x = f x' → x = x') →
    has_card A a →
    has_card B a := begin
    assume A1 A2 A3 h4,
    simp[has_card],
    have exh: ∃ L: (list α) , list.length L = a ∧ (∀ x : α , x ∈ A ↔ x ∈ L)
            ∧ list.nodup L, from h4,
    apply exists.elim exh,
    {
        assume L, assume hL: list.length L = a ∧ (∀ x : α , x ∈ A ↔ x ∈ L)
            ∧ list.nodup L,
        let fL: list β := list.map f L,
        have B1: list.length fL = a, from sorry,
        have B2: (∀ x : β , x ∈ B ↔ x ∈ fL), from sorry,
        have B3: list.nodup fL, from sorry,
        exact ⟨fL, and.intro B1 (and.intro B2 B3)⟩,
    }
    end

theorem card_split
    {α : Type} (A : set α) (B : set α) (C : set α) (b : ℕ) (c : ℕ) :
    (∀ x , x ∈ A → (x ∈ B ∨ x ∈ C)) → 
    (∀ x , ¬ (x ∈ B ∧ x ∈ C)) → 
    has_card B b ->
    has_card C c ->
    has_card A (b+c) := sorry

theorem card_split_map
    {α : Type} {β : Type} {γ : Type}
        (A : set α) (B : set β) (C : set γ) (b : ℕ) (c : ℕ)
        (f : (β → α)) (g : (γ → α)) : 
    (∀ y , y ∈ B → f y ∈ A) →
    (∀ z , z ∈ C → g z ∈ A) → 
    (∀ x , x ∈ A → (∃ y:β , y ∈ B ∧ f y = x) ∨ (∃ z:γ , z ∈ C ∧ g z = x)) → 
    (∀ y z , (y ∈ B → z ∈ B → f y = f z → y = z )) →
    (∀ y z , (y ∈ C → z ∈ C → g y = g z → y = z )) →
    (∀ y z , (y ∈ B → z ∈ C → f y = g z → false)) →
    has_card B b ->
    has_card C c ->
    has_card A (b+c) := sorry

theorem card_0
    {α : Type} (A : set α) :
    (∀ (y:α) , y ∈ A → false) →
    has_card A 0 := 
    begin
    intro h,
    have h0: list.length ([]: list α) = 0, by rw[list.length],
    have h1: (∀ x : α , x ∈ A ↔ x ∈ ([]: list α)), 
        by {intro x, split, 
            {intro xh, apply h x xh},
            intro xh, simp at xh, contradiction},
    have h2: list.nodup ([]: list α), by simp,
    exact ⟨([]: list α), and.intro h0 (and.intro h1 h2)⟩ 
    end

theorem card_1
    {α : Type} (A : set α) (x : α) :
    (x ∈ A) →
    (∀ (y:α) , y ∈ A → x = y) →
    has_card A 1 := 
    begin
    intro h,
    intro hall,
    have h0: list.length (x::[]) = 1, by simp,
    have h1: (∀ z : α , z ∈ A ↔ z ∈ (x::[])), 
        by {intro z, split, 
            {intro zh, have newh: x = z, by apply hall z zh, simp *},
            intro zh, simp at zh, simp *},
    have h2: list.nodup (x::[]), by simp,
    exact ⟨(x::[]), and.intro h0 (and.intro h1 h2)⟩
    end

theorem card_product
    {α : Type} {β : Type} {γ : Type}
        (A : set α) (B : set β) (C : set γ) (a : ℕ) (b : ℕ)
        (f : α → β → γ) :
    (∀ x y , x ∈ A → y ∈ B → f x y ∈ C) →
    (∀ z , z ∈ C → ∃ x y , x ∈ A ∧ y ∈ B ∧ f x y = z) → 
    (∀ (x:α) (y:β) (x':α) (y':β) , x ∈ A → x' ∈ A → y ∈ B → y' ∈ B →
            f x y = f x' y' → x = x' ∧ y = y') →
    has_card A a →
    has_card B b →
    has_card C (a * b) := sorry 

theorem card_product_nat
    {α : Type} {γ : Type}
        (A : set α) (b : ℕ) (C : set γ) (a : ℕ)
        (f : α → ℕ → γ) :
    (∀ x y , x ∈ A → 0 ≤ y → y < b → f x y ∈ C) →
    (∀ z , z ∈ C → ∃ x y , x ∈ A ∧ 0 ≤ y ∧ y < b ∧ f x y = z) → 
    (∀ (x:α) (y:ℕ) (x':α) (y':ℕ) ,
            x ∈ A → x' ∈ A → 0 ≤ y → y < b → 0 ≤ y' → y' < b →
            f x y = f x' y' → x = x' ∧ y = y') →
    has_card A a →
    has_card C (a * b) := sorry

theorem cardinality_unique {α : Type} (A : set α) (a:ℕ) (b:ℕ) :
    has_card A a → has_card A b → a = b := sorry

/-
    Here we define the set of boolean sequences of length n with
    exactly k elements set to `tt`.
    We show that the cardinality of this set is `choose n k`.
    (theorem `has_card_set_n_choose_k`).
-/

def count_tt : (list bool) → (ℕ)
| [] := 0
| (ff :: l) := count_tt l
| (tt :: l) := count_tt l + 1

def set_n_choose_k (n : ℕ) (k : ℕ) : set (list bool) :=
    { l : list bool | list.length l = n ∧ count_tt l = k }

def all_ff : (ℕ) → (list bool)
| 0 := []
| (n + 1) := ff :: (all_ff n)

theorem is_all_ff : ∀ x : (list bool),
    count_tt x = 0 → x = all_ff (list.length x)
    | [] := by simp[count_tt, all_ff]
    | (tt :: l) := by simp[count_tt]
    | (ff :: l) := λ h: count_tt (ff::l) = 0, 
    have h0: 0 = count_tt (ff::l), by simp[refl, h],
    have h1: count_tt (ff::l) = count_tt l, by simp[count_tt], 
    have h2: count_tt l = 0, by simp[h0, h1, refl],
    have h3: l = all_ff (list.length l), by apply (is_all_ff l) h2,
    have h5: list.length (ff :: l) = list.length l + 1, by simp[list.length],
    have h6: all_ff (list.length (ff :: l)) 
        = all_ff(list.length l + 1), by simp[*],
    begin
    have h7:  all_ff (list.length (ff :: l)) = ff :: l, by
    {calc
        all_ff (list.length (ff :: l)) = all_ff (list.length l + 1): by simp[*]
                            ... = ff::(all_ff (list.length l)): by rw[all_ff]
                            ... = ff :: l : by rw[←h3]},
    apply eq.symm h7
    end
    
theorem length_all_ff : ∀ n : ℕ ,
    list.length (all_ff n) = n
    | 0 := by simp[all_ff, refl]
    | (n + 1) := by simp[all_ff, list.length_cons, length_all_ff n]

theorem count_tt_all_ff : ∀ n : ℕ ,
    count_tt (all_ff n) = 0
    | 0 := by simp[count_tt, all_ff, refl]
    | (n+1) := 
        begin
            calc
            count_tt (all_ff (n + 1)) = count_tt (ff:: (all_ff n)): by simp[all_ff]
                                ... = count_tt(all_ff n): by simp[count_tt]
                                ... = 0: by simp[count_tt_all_ff n]
        end

theorem eq_of_add_1 : ∀ n : ℕ , ∀ m : ℕ ,
    (n + 1) = (m + 1) -> n = m := by simp[refl]

theorem has_card_set_n_choose_k : ∀ (n : ℕ) (k : ℕ) ,
    has_card (set_n_choose_k n k) (choose n k)
| n 0 :=
    begin
        rw [has_card, set_n_choose_k] ,
        existsi ([all_ff n]) ,
        split ,
        simp ,
        intros ,
        split ,
        intros ,
        cases a ,
        simp ,
        subst n ,
        apply is_all_ff , assumption ,
        intros ,
        simp at a ,
        simp ,
        subst x ,
        split ,
        apply length_all_ff ,
        apply count_tt_all_ff ,
    end
| 0 (k + 1) :=
    begin
        simp [has_card, set_n_choose_k] ,
        existsi ([]) ,
        split ,
        refl ,
        intros , split ,
        intros ,
        simp ,
        cases a ,
        have h : (x = list.nil) ,
        cases x , trivial, trivial ,
        subst x at a_right , simp [count_tt] at a_right , trivial ,
        simp ,
    end
| (n+1) (k+1) :=
    begin
        simp [set_n_choose_k] ,
        apply (card_split_map
            ({l : list bool | list.length l = n + 1 ∧ count_tt l = k + 1})
            ({l : (list bool) | list.length l = n ∧ count_tt l = k})
            ({l : (list bool) | list.length l = n ∧ count_tt l = k+1})
            (choose n k)
            (choose n (k+1))
            (λ r : (list bool) , ((tt :: r) : list bool))
            (λ r : (list bool) , ((ff :: r) : list bool))
        ) ,
        {
            simp , intros ,
            cases x , trivial ,
            cases x_hd ,
            {
                right , existsi x_tl ,
                split , split ,
                simp at a , rw [@nat.add_comm 1 _] at a ,
                apply eq_of_add_1 , assumption ,
                simp [count_tt] at a_1 , assumption ,
                trivial ,
            },
            {
                left , existsi x_tl ,
                split , split ,
                simp at a , rw [@nat.add_comm 1 _] at a ,
                apply eq_of_add_1 , assumption ,
                simp [count_tt] at a_1 , assumption ,
                trivial ,
            }
        },
        {
            intros ,
            simp at a_2 ,
            assumption ,
        },
        {
            intros ,
            simp at a_2 ,
            assumption ,
        },
        {
            intros ,
            simp at a_2 ,
            assumption ,
        },
        {
            apply has_card_set_n_choose_k ,
        },
        {
            apply has_card_set_n_choose_k ,
        },
    end

