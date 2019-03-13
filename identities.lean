import data.nat.choose
import data.set
import data.set.finite
import data.multiset
import data.list

open list

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

def count_tt : (list bool) -> ℕ
    | [] := 0
    | (ff :: l) := count_trues l
    | (tt :: l) := count_trues l + 1

def set_n_choose_k (n : ℕ) (k : ℕ) : set (list bool) :=
    { l : list bool | length l = n ∧ count_tt l = k }

def all_ff : (ℕ) → (list bool)
| 0 := []
| (n + 1) := ff :: (all_ff n)

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
    end
    /-
    begin
        rw has_card ,
        existsi ([[]]) ,
        split ,
        simp ,
        intros ,
        split ,
        intros ,
        simp [set_n_choose_k] at a ,
        cases a ,
        simp ,
        cases x , trivial , trivial ,
        intros ,
        simp at a ,
        simp [set_n_choose_k] ,
        subst x , 
        split , refl , refl ,
    end
    -/
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
        have h : (x = nil) ,
        cases x , trivial, trivial ,
        subst x at a_right , simp [count_tt] at a_right , trivial ,
        simp ,
    end
| n k := sorry
