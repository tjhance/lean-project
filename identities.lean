import data.nat.choose
import data.set
import data.set.finite
import data.multiset
import data.list

#check set
#check finset ℕ 
#check @finset.mk
#check choose 5 4

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
    has_card B a := sorry

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
    has_card A 0 := sorry

theorem card_1
    {α : Type} (A : set α) (x : α) :
    (x ∈ A) →
    (∀ (y:α) , y ∈ A → x = y) →
    has_card A 1 := sorry

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

def count_tt : (list bool) -> ℕ
    | [] := 0
    | (ff :: l) := count_tt l
    | (tt :: l) := count_tt l + 1

def set_n_choose_k (n : ℕ) (k : ℕ) : set (list bool) :=
    { l : list bool | list.length l = n ∧ count_tt l = k }

def all_ff : (ℕ) → (list bool)
| 0 := []
| (n + 1) := ff :: (all_ff n)

/- Lean really doesn't like my is_all_ff proof so maybe it should just be reworked completely.
I'm not convinced I had the winning strategy lol -/
theorem is_all_ff_aux : ∀ x : (list bool), all_ff (list.length x + 1) = ff:: (all_ff (list.length x))
| [] := by simp[all_ff]
| (a::l) := by rw[all_ff]

theorem is_all_ff : ∀ x : (list bool),
    count_tt x = 0 → x = all_ff (list.length x)
    | [] := by simp[count_tt, all_ff]
    | (tt :: l) := by simp[count_tt]
    | (ff :: l) := λ h: count_tt (ff::l) = 0, 
    have h0: 0 = count_tt (ff::l), by simp[refl, h],
    have h1: count_tt (ff::l) = count_tt l, by simp[count_tt], 
    have h2: count_tt l = 0, by simp[h0, h1, refl],
    have h3: count_tt l = 0 → l = all_ff (list.length l), by apply is_all_ff l,
    have h4: l = all_ff (list.length l), by apply h3 h2,
    have h5: list.length (ff :: l) = list.length l + 1, by simp[list.length],
    have h6: all_ff (list.length (ff :: l)) 
        = all_ff(list.length l + 1), by simp[*],
    begin
    have h7:  all_ff (list.length (ff :: l)) = ff :: l, by
    {calc
        all_ff (list.length (ff :: l)) = all_ff (list.length l + 1): by simp[*]
                            ... = ff::(all_ff (list.length l)): by apply is_all_ff_aux l
                            ... = ff :: l : by rw[←h4]},
    have h8: all_ff (list.length l + 1) = ff :: l, by
    {calc
        all_ff (list.length l + 1) = ff::(all_ff (list.length l)): by apply is_all_ff_aux l
                            ... = ff :: l : by rw[←h4]},
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
            ({l : (list bool) | length l = n ∧ count_tt l = k})
            ({l : (list bool) | length l = n ∧ count_tt l = k+1})
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

