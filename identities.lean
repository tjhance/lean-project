import data.nat.choose
import data.set
import data.set.finite
import data.multiset
import data.list

#check set
#check finset ℕ 
#check @finset.mk
#check choose 5 4

/-
#check finset.mk (multiset.zero) multiset.nodup_zero

def zero_finset := finset.mk (@multiset.zero ℕ) multiset.nodup_zero

#eval finset.card zero_finset

def finset_is {α : Type} (s : finset α) (m : α → Prop) : Prop :=
    ∀ x : α , (x ∈ s) ↔ m x

def list_n_choose_k : (ℕ) -> (ℕ) -> list (list bool)
| 0 0 := [[]]
| 0 k := []
| n k := 
    list.map (λ l , true :: l) (list_n_choose_k (n-1)) ++
    list.map (λ l , true :: l) (list_n_choose_k (n-1))

def finset_n_choose_k (n : ℕ) (k : ℕ) : finset (list bool) :=
    finset.mk (h)
-/

def has_card {α : Type} (s : set α) (n : ℕ) : Prop :=
    ∃ l : (list α) , length l = n ∧ (∀ x : α , x ∈ s ↔ x ∈ l)
            ∧ list.nodup l

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
    (∀ x , x ∈ A → (∃ y:β , y ∈ B ∧ f y = x) ∨ (∃ z:γ , z ∈ C ∧ g z = x)) → 
    (∀ y z , (y ∈ B → z ∈ B → f y = f z → y = z )) →
    (∀ y z , (y ∈ C → z ∈ C → g y = g z → y = z )) →
    (∀ y z , (y ∈ B → z ∈ C → f y = g z → false)) →
    has_card B b ->
    has_card C c ->
    has_card A (b+c) := sorry

def count_tt : (list bool) -> ℕ
    | [] := 0
    | (ff :: l) := count_tt l
    | (tt :: l) := count_tt l + 1

def set_n_choose_k (n : ℕ) (k : ℕ) : set (list bool) :=
    { l : list bool | list.length l = n ∧ count_tt l = k }

def all_ff : (ℕ) → (list bool)
| 0 := []
| (n + 1) := ff :: (all_ff n)

theorem is_all_ff : ∀ x : (list bool) ,
    count_tt x = 0 -> x = all_ff (list.length x) := sorry
    
theorem length_all_ff : ∀ n : ℕ ,
    list.length (all_ff n) = n := sorry

theorem count_tt_all_ff : ∀ n : ℕ ,
    count_tt (all_ff n) = 0
    | 0 := 
        begin 
            simp[count_tt, all_ff, refl]
        end
    | (n+1) := 
        begin
            sorry
        end

theorem eq_of_add_1 : ∀ n : ℕ , ∀ m : ℕ ,
    (n + 1) = (m + 1) -> n = m := sorry

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
            ({l : list bool | length l = n + 1 ∧ count_tt l = k + 1})
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

