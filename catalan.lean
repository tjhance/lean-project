import project.identities
import tactic.linarith
import tactic.tidy
import data.list
import data.list.basic
import data.int.basic
import tactic.ring
import data.nat.gcd

/-
    Catalan numbers.

    In this file we:

        - Define `balanced`: balanced strings of parentheses
          (`tt` is   and open paren, `ff` is a close paren).

        - Define `catalan`: the catalan numbers by recurrence

        - Show that the set of balanced strings of length 2*n
          is catalan n. (theorem `has_card_set_balanced`)
          by induction, by showing that a balanced string of
          length 2*(m+1) corresponds to a pair of balanced
          strings whose lengths sum to 2*m.

        - Define `below_diagonal_path`, a proposition which
          indicates that a path of length (2n+1) goes from
          (0,0) to (n,n+1) while never going above the
          (0,0)--(n,n+1) diagonal.
        
        - Show that balanced strings of length 2*n are in bijection
          with below_diagonal_path strings of length 2*n+1.
          (theorem `has_card_set_below_diagonal_path_catalan`)
        
        - Take all 2*n+1 rotations of all below_diagonal_path
          strings, and show that this gives *all* paths
          from (0,0) to (n,n+1)
          (theorem `theorem has_card_set_n_choose_k_catalan`)
        
        - Finally, show that
            catalan n = (choose (2*n+1) n) / (2*n + 1)
          (theorem `catalan_identity`)

    We define `catalan` by recurence, then show that `catalan n`
    is the cardinality of the set of balanced strings of length 2n.
    (theorem `has_card_set_balanced`)

    Then by doing a bijection through paths from (0,0) to (n,n+1),
    we prove our main result, the theorem
    `catalan_identity`.
-/

/-
    Define balanced strings of parentheses.
    `tt` represents an open paren, `ff` represents a closed paren.
-/

def balanced_aux : (list bool) → (ℕ) → Prop
    | [] 0 := true
    | [] (d + 1) := false
    | (tt :: l) d := balanced_aux l (d + 1)
    | (ff :: l) 0 := false
    | (ff :: l) (d + 1) := balanced_aux l d

def balanced (l : list bool) : Prop := balanced_aux l 0

/-
    Define the set of balanced parentheses of length 2*n
    (that is, n pairs of parentheses)
-/

def set_balanced (n : ℕ) : set (list bool) :=
    { l : list bool | list.length l = 2 * n ∧ balanced l }

/-
    Define the catalan numbers
-/

def sum_to : Π (n:ℕ) , (Π (x:ℕ) , (x<n) → ℕ) → ℕ
    | 0 f := 0
    | (n+1) f :=
        have h : n < (n+1) , by linarith ,
        have f' : (Π (x:ℕ) , (x<n) → ℕ) , from 
            (λ x , λ ineq , f x (by linarith)) ,
        f n h + sum_to n f'

def catalan : ℕ → ℕ
    | 0 := 1
    | (n+1) := sum_to (n+1) (λ i , λ i_le_n ,
            have nmi_le_n : (n-i < (n+1)),
                by apply nat.sub_lt_succ ,
            catalan i * catalan (n-i)
        )

/- split (A)B into A, B -/
def split_parens_aux : (list bool) → (ℕ) → (list bool × list bool)
| ([]) n := ([],[])
| (ff :: l) 0 := ⟨ [], [] ⟩ /- doesn't matter -/
| (ff :: l) 1 := ⟨ [], l ⟩
| (ff :: l) (d + 2) := let p := split_parens_aux l (d+1) in ⟨ ff :: p.1 , p.2 ⟩
| (tt :: l) (d) := let p := split_parens_aux l (d+1) in ⟨ tt :: p.1 , p.2 ⟩
def split_parens : (list bool) → (list bool × list bool)
| [] := ([],[]) /- doesn't matter -/
| (tt :: l) := split_parens_aux l 1
| (ff :: l) := ([],[]) /- doesn't matter -/

/- combined A, B into (A)B -/
def combine_parens (l : list bool) (m : list bool) : (list bool) :=
    tt :: l ++ ff :: m

/- lemmas about balanced parentheses -/

theorem balanced_split_parens_2_aux : ∀ (l:list bool) (d:ℕ) ,
    balanced_aux l d -> balanced (split_parens_aux l d).2
    | [] 0 :=
    begin
        intros ,
        rw [split_parens_aux] , simp ,
    end
    | [] (d + 1) :=
    begin
        intros ,
        rw [balanced_aux] at * , contradiction ,
    end
    | (tt :: l) d :=
    begin
        intros , rw [balanced_aux] at * ,
        rw [split_parens_aux] ,
        simp ,
        apply balanced_split_parens_2_aux , assumption ,
    end
    | (ff :: l) 0 :=
    begin
        intros ,
        rw [split_parens_aux, balanced], simp ,
    end
    | (ff :: l) (d + 1) :=
    begin
        intros ,
        cases d,
        {
            simp , rw [split_parens_aux] , simp ,
            rw [balanced_aux] at a , rw [balanced] , assumption ,
        },
        {
            rw [split_parens_aux] , simp ,
            apply balanced_split_parens_2_aux ,
            rw [balanced_aux] at a,
            have h : (d + 1) = nat.succ d := rfl ,
            rw [h] , assumption ,
        }
    end

theorem balanced_split_parens_1_aux : ∀ (l:list bool) (d:ℕ) ,
    balanced_aux l (d+1) -> balanced_aux (split_parens_aux l (d+1)).1 d
    | [] 0 :=
    begin
        intros ,
        rw [split_parens_aux] , simp ,
    end
    | [] (d + 1) :=
    begin
        intros ,
        rw [balanced_aux] at * , contradiction ,
    end
    | (tt :: l) d :=
    begin
        intros ,
        rw [split_parens_aux] , simp ,
        apply balanced_split_parens_1_aux , 
        rw [balanced_aux] at a , assumption ,
    end
    | (ff :: l) 0 :=
    begin
        intros ,
        rw [split_parens_aux] , simp , 
    end
    | (ff :: l) (d + 1) :=
    begin
        intros ,
        rw [split_parens_aux] , simp , rw [balanced_aux] ,
        apply balanced_split_parens_1_aux ,
        rw [balanced_aux] at a ,
        assumption ,
    end

theorem balanced_split_parens_1 : ∀ (l : list bool) ,
    balanced l -> balanced (split_parens l).1 :=
    begin
        intros ,
        rw [balanced] ,
        cases l ,
        {
            rw [split_parens, balanced_aux] , trivial ,
        },
        cases l_hd ,
        {
            rw [balanced] at a,
            rw [balanced_aux] at a ,
            contradiction ,
        },
        {
            rw [split_parens] ,
            apply balanced_split_parens_1_aux ,
            rw [balanced] at a , rw [balanced_aux] at a ,
            assumption ,
        }
    end

theorem balanced_split_parens_2 : ∀ (l : list bool) ,
    balanced l -> balanced (split_parens l).2 :=
    begin
        intros ,
        rw [balanced] ,
        cases l ,
        {
            rw split_parens , simp , 
        },
        cases l_hd ,
        {
            rw [balanced] at a,
            rw [balanced_aux] at a ,
            contradiction ,   
        },
        {
            apply balanced_split_parens_2_aux ,
            rw [balanced, balanced_aux] at a , simp at a , assumption ,
        }
    end

theorem balanced_combine_aux : ∀ (l : list bool) (m : list bool) (d:ℕ) ,
    balanced_aux l d →
    balanced m →
    balanced_aux (l ++ ff :: m) (d+1)
| [] m :=
    begin
        intros , simp , rw [balanced_aux] ,
        cases d ,
        {
            rw [balanced] at a_1 , assumption ,
        },
        {
            rw [balanced_aux] at a , contradiction ,
        }
    end
| (x :: l) m :=
    begin
        intros ,
        cases x ,
        {
            have h : (ff :: l ++ ff :: m = ff :: (l ++ ff :: m)) := by simp,
            rw h ,
            rw [balanced_aux] ,
            cases d ,
            {
                rw [balanced_aux] at a , contradiction ,
            },
            {
                apply balanced_combine_aux ,
                rw [balanced_aux] at a , assumption ,
                assumption ,
            }
        },
        {
            have h : (tt :: l ++ ff :: m = tt :: (l ++ ff :: m)) := by simp,
            rw h ,
            rw [balanced_aux] ,
            apply balanced_combine_aux ,
            rw [balanced_aux] at a , assumption,
            assumption,
        }
    end

theorem balanced_combine : ∀ (l : list bool) (m : list bool) ,
    balanced l →
    balanced m →
    balanced (combine_parens l m) :=
begin
    intros , rw [combine_parens] , 
    rw [balanced] ,
    have h : (tt :: l ++ ff :: m = tt :: (l ++ ff :: m)) := by simp,
    rw h ,
    rw [balanced_aux] ,
    apply balanced_combine_aux ,
    rw [balanced] at a ,
    assumption ,
    assumption ,
end

theorem split_parens_combine_parens_aux : ∀ (l : list bool) (m : list bool) (d:ℕ) ,
    balanced_aux l d →
    balanced m →
    split_parens_aux (l ++ ff :: m) (d+1) = ⟨l, m⟩
| [] m 0 :=
    begin
        intros , simp [split_parens_aux] ,
    end
| [] m (d + 1) :=
    begin
        intros , simp [balanced_aux] at a , contradiction ,
    end
| (tt :: l) m d :=
    begin
        intros ,
        simp [split_parens_aux] ,
        have q : balanced_aux l (d+1) := begin
            rw [balanced_aux] at a , assumption ,
        end,
        have h := split_parens_combine_parens_aux l m (d+1) q a_1,
        simp at h , rw h , simp , 
    end
| (ff :: l) m 0 :=
    begin
        intros ,
        simp [balanced_aux] at a , contradiction ,
    end
| (ff :: l) m (d + 1) :=
    begin
        intros ,
        simp [split_parens_aux] ,
        have q : balanced_aux l d := begin
            rw [balanced_aux] at a , assumption ,
        end,
        have h := split_parens_combine_parens_aux l m d q a_1,
        rw h , simp , 
    end

theorem split_parens_combine_parens : ∀ (l : list bool) (m : list bool) ,
    balanced l →
    balanced m →
    split_parens (combine_parens l m) = ⟨l, m⟩ :=
begin
    intros ,
    rw [combine_parens],
    have h : (tt :: l ++ ff :: m = tt :: (l ++ ff :: m)) := by simp,
    rw h,
    rw [split_parens] ,
    apply split_parens_combine_parens_aux ,
    rw [balanced] at a , assumption ,
    assumption ,
end

theorem combine_parens_split_parens_aux : ∀ (l : list bool) (d:ℕ) ,
    balanced_aux l (d+1) →
    (split_parens_aux l (d+1)).1 ++ ff :: (split_parens_aux l (d+1)).2 = l
| [] d :=
    begin
        intros , rw [balanced_aux] at a , contradiction ,
    end
| (tt :: l) d :=
    begin
        intros ,
        rw [split_parens_aux] , simp ,
        rw [balanced_aux] at a ,
        have h := combine_parens_split_parens_aux l (d+1) a,
        simp at a h, assumption,
    end
| (ff :: l) 0 :=
    begin
        intros , rw [balanced_aux] at a ,
        rw [split_parens_aux] , simp ,
    end
| (ff :: l) (d+1) :=
    begin
        intros ,
        rw [split_parens_aux] , simp ,
        rw [balanced_aux] at a ,
        have h := combine_parens_split_parens_aux l d a,
        assumption,
    end

theorem combine_parens_split_parens : ∀ (l : list bool) ,
    balanced l →
    ¬(l = list.nil) → 
    combine_parens (split_parens l).1 (split_parens l).2 = l :=
begin
    intros ,
    cases l ,
    simp at a_1, contradiction ,
    cases l_hd ,
    rw [balanced, balanced_aux] at a , contradiction ,
    rw [split_parens] , rw [combine_parens] , simp ,
    apply combine_parens_split_parens_aux ,
    simp , rw [balanced] at a , rw [balanced_aux] at a , simp at a ,
    assumption ,
end

theorem length_combine_parens : ∀ (l : list bool) (m : list bool) ,
    balanced l →
    balanced m →
    list.length (combine_parens l m) = list.length l + list.length m + 2
    :=
begin
    intros , rw [combine_parens] , simp , rw [<- add_assoc] , simp ,
end

theorem length_split_parens_eq_minus : ∀ (l : list bool) (n:ℕ) (a:ℕ) ,
    list.length l = 2 * (n + 1) → 
    balanced l →
    list.length ((split_parens l).1) = 2 * a →
    list.length ((split_parens l).2) = 2 * (n - a) :=
begin
    intros ,
    have h :
        list.length (combine_parens (split_parens l).1 (split_parens l).2) = list.length (split_parens l).1 +
          list.length (split_parens l).2 + 2 :=
        begin
            apply length_combine_parens ,
            apply balanced_split_parens_1 , assumption ,
            apply balanced_split_parens_2 , assumption ,
        end,
    calc list.length ((split_parens l).2) =
        list.length (split_parens l).1 + list.length (split_parens l).2 + 2 -
        (list.length (split_parens l).1 + 2) : begin
            rw [@nat.add_comm (list.length ((split_parens l).fst)) _] ,
            rw nat.add_assoc ,
            rw nat.add_sub_cancel ,
        end
    ... = list.length (
            combine_parens (split_parens l).1 (split_parens l).2) - (list.length (split_parens l).1 + 2) : by rw h 
    ... = list.length l - (list.length (split_parens l).1 + 2) :
        begin
            rw combine_parens_split_parens , assumption ,
            apply not.intro , intros , subst l , simp at a_1,
            contradiction ,
        end
    ... = list.length l - (2 * a + 2) : by rw a_3
    ... = 2 * (n + 1) - (2 * a + 2) : by rw a_1
    ... = 2 * (n + 1) - (2 * a + 2 * 1) : by simp
    ... = 2 * (n + 1) - 2 * (a + 1) : by rw [mul_add 2 a 1]
    ... = 2 * ((n+1) - (a+1)) : by rw [nat.mul_sub_left_distrib 2 (n+1) (a+1)]
    ... = 2 * (n - a) : by simp
end

theorem even_length_of_balanced_aux : ∀ (l : list bool) (d : ℕ) ,
    balanced_aux l d → 
    (∃ m , list.length l + d = 2 * m)
    | [] 0 :=
    begin
        intros , existsi 0 , simp ,
    end
    | [] (d + 1) :=
    begin
        intros , rw [balanced_aux] at a , contradiction ,
    end
    | (tt :: l) d :=
    begin
        intros ,
        rw [balanced_aux] at a ,
        have h := even_length_of_balanced_aux l (d+1) a ,
        cases h ,
        existsi h_w ,
        simp ,
        simp at h_h , assumption ,
    end
    | (ff :: l) 0 :=
    begin
        intros , rw [balanced_aux] at a , contradiction ,
    end
    | (ff :: l) (d + 1) :=
    begin
        intros ,
        rw [balanced_aux] at a ,
        have h := even_length_of_balanced_aux l d a ,
        cases h ,
        existsi (h_w + 1) ,
        rw [mul_add] , simp , rw <- h_h , simp ,
        rw [<- add_assoc] , simp ,
    end

theorem even_length_of_balanced : ∀ (l : list bool) ,
    balanced l →
    2 ∣ list.length l
    :=
begin
    intros ,
    rw [balanced] at a ,
    have h := even_length_of_balanced_aux l 0 a ,
    cases h ,
    simp at h_h ,
    rw h_h ,
    apply dvd_mul_right ,
end

theorem length_split_parens_1_le : ∀ (l : list bool) ,
    balanced l →
    ¬(l = list.nil) →
    list.length (split_parens l).1 ≤ list.length l - 2 :=
begin
    intros ,
    have h : (combine_parens (split_parens l).1 (split_parens l).2 = l)
        := combine_parens_split_parens l a a_1 ,
    have h2 : (list.length (combine_parens (split_parens l).1 (split_parens l).2) = list.length (split_parens l).1 + list.length (split_parens l).2 + 2)
        :=
    begin
        apply length_combine_parens ,
        apply balanced_split_parens_1 , assumption ,
        apply balanced_split_parens_2 , assumption ,
    end,
    rw h at h2 ,
    calc list.length ((split_parens l).fst)
        ≤ list.length ((split_parens l).fst) + list.length ((split_parens l).snd) : by linarith 
    ... = list.length ((split_parens l).fst) + list.length ((split_parens l).snd) + 2 - 2 : by simp
    ... = list.length l - 2 : by rw h2
end

lemma catalan_set_eq_with_bound : ∀ (n:ℕ) ,
    {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l} = 
    {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*(n+1)} :=
begin
    intros , 
    apply set.ext ,
    intros , split ,
    {
        intros ,
        split ,
        cases a, assumption ,
        split ,
        cases a , assumption ,
        simp at a , cases a , 
        calc list.length (split_parens x).1 ≤ (list.length x) - 2
                : (begin
                    apply length_split_parens_1_le , assumption ,
                    apply not.intro , intros , subst x , simp at a_left , trivial ,
                  end)
            ... = 2 * n
                : (begin
                    rw a_left,
                    rw mul_add , simp ,
                  end)
            ... < 2 * (n + 1)
                : by linarith
    },
    {
        intros ,
        cases a , cases a_right , simp , split , assumption ,
        assumption ,
    }
end 

/- annoying arithmetic lemmas -/

theorem nat_lt_of_not_eq : ∀ (n:ℕ) (m:ℕ) ,
    n < m+1 → ¬(n = m) → n < m :=
begin
    intros ,
    by_contradiction ,
    have h : (n = m) := nat.eq_of_lt_succ_of_not_lt a a_2 ,
    contradiction ,
end

theorem even_nat_lt : ∀ (n:ℕ) (m:ℕ) ,
    (n) < 2*(m + 1) → 
    ¬ ((n) = 2*m) →
    2 ∣ n → 
    n < 2*m :=
begin
    intros ,
    by_cases (n = 2 * m + 1) ,
    { 
        subst n ,
        /- derive a contradiction from 2 | 2*m + 1
           (surely there was an easier way to do this?) -/
        have h : (2 ∣ (2 * int.of_nat m)) := dvd_mul_right _ _,
        have h1 : (2 ∣ (2 * int.of_nat m) + 1) := begin
            have h3 : (2 ∣ int.of_nat (2*m + 1)) :=
                begin
                    apply int.of_nat_dvd_of_dvd_nat_abs ,
                    simp , simp at a_2 , assumption ,
                end,
            have two_eq : 2 = int.of_nat 2 := by refl ,
            rw two_eq ,
            have one_eq : 1 = int.of_nat 1 := by refl ,
            rw one_eq ,
            rw <- int.of_nat_mul ,
            rw <- int.of_nat_add ,
            assumption ,
        end,
        have h2 : (2 ∣ ((2 * int.of_nat m) + 1) - (2 * int.of_nat m)) :=
            begin
                apply dvd_sub , assumption , assumption ,
            end,
        simp at h2,
        have h3 : ((1:int) % 2 = 0) := begin
                apply int.mod_eq_zero_of_dvd , assumption ,
            end,
        have h4 : ((1:int) % 2 = 1) := rfl ,
        rw h4 at h3 ,
        simp at h3 ,
        contradiction ,
    },
    {
        have i : (2*(m+1) = (2*m + 1) + 1) := begin
            rw [mul_add] , simp , rw [<- @nat.add_assoc 1 _] ,
        end,
        have j : (n < ((2*m) + 1) + 1) := begin
            rw <- i , assumption ,
        end ,
        have k : (n < (2*m) + 1) := nat_lt_of_not_eq _ _ j h ,
        have l : (n < (2*m)) := nat_lt_of_not_eq _ _ k a_1 ,
        assumption ,
    }
end

lemma catalan_set_induction : ∀ (n:ℕ) (i:ℕ) (a:ℕ) (b:ℕ) ,
    has_card {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*i} a →
    has_card {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 = 2*i} b →
    has_card {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*(i+1)} (a+b) :=
begin
    intros ,
    apply card_split _ 
        {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*i}
        {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 = 2*i}
        a b ,
    {
        intros , simp , simp at a_3 , cases a_3 , cases a_3_right ,
        split, assumption , split, assumption , linarith , 
    },
    {
        intros , simp , simp at a_3 , cases a_3 , cases a_3_right ,
        split, assumption , split, assumption , linarith , 
    },
    {
        simp ,
        intros ,
        by_cases (list.length (split_parens x).1 = 2*i) ,
        {
            right , split, assumption, split, assumption, assumption ,
        },
        {
            left, split, assumption, split, assumption, 
            apply even_nat_lt ,
            assumption ,
            assumption ,
            apply even_length_of_balanced ,
            apply balanced_split_parens_1 ,
            assumption ,
        }
    },
    {
        simp , intros ,
        apply not.intro , intros , 
        rw a_8 at a_5 ,
        linarith ,
    },
    {
        assumption ,
    },
    {
        assumption ,
    },
end

lemma catalan_set_base : ∀ (n:ℕ) ,
    has_card {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*0} 0 :=
begin
    intros,
    apply card_0 ,
    simp ,
end

/-
    Show that balanced parentheses have cardinality the catalan
    numbers by splitting the parentheses strings into pairs.
    We do induction on `bound`.
-/

lemma has_card_set_balanced_aux : ∀ bound n ,
    n < bound →
    has_card (set_balanced n) (catalan n)
| 0 n :=
    begin
        intros ,
        linarith ,
    end
| (bound+1) 0 :=
    begin
        intros ,
        rw [set_balanced, catalan] ,
        apply (card_1 _ []) ,
        simp ,
        intros , simp at a_1 , cases a_1 , cases y ; trivial ,
    end
| (bound+1) (n+1) :=
    begin
        intros , 
        rw catalan ,
        rw set_balanced ,

        /- add the bound that the first part of the split is < 2*(n+1) -/
        rw catalan_set_eq_with_bound ,

        /- replace n+1 with j (why is this so annoying omg) -/
        have j' : (∃ j , j = n+1) , existsi (n+1), trivial, cases j', rename j'_w j ,
        have e : (
            {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧ list.length ((split_parens l).fst) < 2 * (n + 1)} =
            {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧ list.length ((split_parens l).fst) < 2 * j}) ,
        rw j'_h ,
        rw e ,
        clear e ,
        have e : (
                sum_to (n + 1) (λ (i : ℕ) (i_le_n : i < n + 1), catalan i * catalan (n - i))
                 =
                sum_to j (λ (i : ℕ) (i_le_n : i < j), catalan i * catalan (n - i))) := by rw j'_h,
        rw e , clear e,
        have n_bound : (n+1) < (bound+1) := a , /- copy this -/
        have j_bound : j ≤ (n+1) := 
            begin
                subst j , 
            end ,
        clear a , clear j'_h ,

        /- do induction on j for the summation of the recursion -/
        induction j, 
        {
            rw [sum_to] ,
            apply catalan_set_base ,
        },
        {
            rw [sum_to] , simp ,
            rw [@nat.add_comm (catalan j_n * catalan (n - j_n)) _] ,
            apply catalan_set_induction ,
            {
                apply j_ih ,
                calc j_n ≤ j_n + 1 : by linarith
                ... = nat.succ j_n : by refl 
                ... ≤ n + 1 : by assumption
            },
            {
                /- Show that the length of balanced strings
                   of the form (A)B where |A|=2*j_n is
                   catalan j_n * catalan (n-j_n). -/

                clear j_ih ,
                apply (card_product
                    {l : list bool | list.length l = 2 * j_n ∧      
                        balanced l}
                    {l : list bool | list.length l = 2 * (n - j_n) ∧      
                        balanced l}
                    _
                    (catalan j_n)
                    (catalan (n - j_n))
                    combine_parens
                 ) ,
                 {
                     simp, intros,
                     split ,
                     rw [combine_parens] , simp , rw a , rw a_2 ,
                     {
                        calc 1 + (1 + (2 * j_n + 2 * (n - j_n))) = 2 * (n + 1) : begin
                            rw [<- mul_add] ,
                            rw [add_comm j_n] ,
                            rw [nat.sub_add_cancel] , ring,
                            have h : (nat.succ j_n = j_n + 1) := rfl ,
                            rw h at j_bound , linarith ,
                        end
                     },
                     {
                         split,
                         apply balanced_combine , assumption, assumption ,
                         rw split_parens_combine_parens , simp , assumption ,
                         assumption, assumption,
                     }
                 },
                 {
                    simp, intros ,
                    existsi (split_parens z).1 ,
                    split ,
                    split , assumption ,
                    apply balanced_split_parens_1 , assumption ,
                    existsi (split_parens z).2 ,
                    split ,
                    split ,
                    apply length_split_parens_eq_minus ; assumption ,
                    apply balanced_split_parens_2 , assumption ,
                    apply combine_parens_split_parens ,
                    assumption ,
                    apply not.intro , intros , subst z , simp at a ,linarith , 
                 },
                 {
                    simp, intros , 
                    have e : (( x, y ) = ( x', y' )) := (
                    calc ( x, y ) = split_parens (combine_parens x y) :
                            (begin
                                rw split_parens_combine_parens ,
                                assumption, assumption ,
                            end)
                        ... = split_parens (combine_parens x' y') :
                            (begin
                                rw a_8 ,
                            end)
                        ... = ( x', y' ) :
                            (begin
                                rw split_parens_combine_parens ,
                                assumption, assumption ,
                            end)),
                    simp at e ,
                    assumption ,
                 },
                 {
                     apply (has_card_set_balanced_aux bound) ,
                     have h : (nat.succ j_n = j_n + 1) := rfl ,
                     rw h at j_bound , linarith ,
                 },
                 {
                     apply (has_card_set_balanced_aux bound) ,
                     have h : (nat.succ j_n = j_n + 1) := rfl ,
                     rw h at j_bound ,
                     have t : (n - j_n ≤ n) := nat.sub_le_self _ _ ,
                     linarith ,
                 },
            }
        }

    end

/- main theorem that balanced parentheses strings of length 2*n
   has cardinality catalan n -/

theorem has_card_set_balanced : ∀ n ,
    has_card (set_balanced n) (catalan n) :=
begin
    intros ,
    apply (has_card_set_balanced_aux (n+1) n) ,
    linarith ,
end

/- below_diagonal_path is a proposition that indicates
   a sequence represents a path
    from (0,0) to (n, n+1) (where tt is +1 in x direction
   and ff is +1 in y direction) which always stays below
   the diagonal.

   We will biject such paths with the balanced parentheses,
   (theorem `has_card_set_below_diagonal_path_catalan`)
   which will show that they have cardinality `catalan n`.

   Then we will show that (2n+1) rotations of
   of these paths will be the set of all paths from (0,0) to (n,n+1),
   which has number (2n+1 choose n).
    -/

def below_diagonal_path (n : ℕ) (l : list bool) :=
    list.length l = 2*n + 1 ∧
    count_tt l = n ∧
    (forall (i:ℕ) , i ≤ (2*n + 1) →
        ((int.of_nat i) * (int.of_nat n) -
            (2*(int.of_nat n)+1) * (int.of_nat (count_tt (list.take i l))) ≤ 0))

def argmax : (ℕ → ℤ) → ℕ → ℕ
    | f 0 := 0
    | f (n+1) := if f (n+1) > f (argmax f n) then (n+1) else argmax f n

/-
    Gets the point on a path from (0,0) to (n,n+1)
    which is farthest above the (0,0)--(n,n+1) diagonal.
    This is important because if we rotate the path to this
    point, then it will be a below_diagonal_path.
    (theorem below_diagonal_path_rotate_best_point).
-/

def best_point (n:ℕ) (l : list bool) :=
    argmax (λ i ,
        (int.of_nat n) * (int.of_nat i) -
            (2*(int.of_nat n) + 1) * (int.of_nat (count_tt (list.take i l)))
    ) (2*n)

/-
    A bunch of lemmas dealing with rotations and argmax and
    miscellaneous. We represent rotations as numbers i
    where 0 ≤ i < n. And implement them as
    `list.drop i l + list.take i l`.
    (In retrospect it might have made more sense to use list.rotate
    more heavily.) 
-/

def negate_rotation (n:ℕ) (i:ℕ) :=
    if i = 0 then 0 else n - i

def compose_rotation (n:ℕ) (i:ℕ) (j:ℕ) :=
    (i + j) % n

theorem argmax_lt_length : ∀ (f : ℕ → ℤ) (n : ℕ) ,
    argmax f n < n+1
| f 0 := begin intros, rw [argmax] , linarith , end
| f (n+1) :=
    begin
        rw argmax ,
        split_ifs ,
        linarith ,
        have h : argmax f n < n + 1 := argmax_lt_length f n ,
        linarith ,
    end

theorem func_argmax_ge : ∀ (f: ℕ → ℤ) (n : ℕ) (i : ℕ) ,
    i ≤ n → 
    f (argmax f n) ≥ f i
| f 0 0 :=
    begin
        intros , rw [argmax] , linarith ,
    end
| f 0 (i+1) :=
    begin
        intros , linarith ,
    end
| f (n+1) i :=
    begin
        intros ,
        {
            rw [argmax] , split_ifs ,
            {
                rename h h' ,
                by_cases (i = n+1) ,
                {
                    subst i , linarith ,
                },
                {
                    apply le_of_lt ,
                    have h2 : (i < n+1) := begin
                        apply nat_lt_of_not_eq, linarith , assumption ,
                    end,
                    calc f i ≤ f (argmax f n) :
                        (begin
                            apply func_argmax_ge ,
                            rw <- nat.lt_succ_iff ,
                            assumption ,
                        end)
                    ... < f (n+1) : h'
                }
            },
            {
                have h' : (f (argmax f n) ≥ f (n + 1)) := begin
                    apply le_of_not_gt , assumption ,
                end,
                by_cases (i=n+1) ,
                {
                    subst i , assumption ,
                },
                {
                    have h2 : (i < n+1) := begin
                        apply nat_lt_of_not_eq, linarith , assumption ,
                    end,
                    rw nat.lt_succ_iff at h2 ,
                    apply func_argmax_ge , assumption,
                }
            },
        }
    end

theorem best_point_gt (n:ℕ) (l : list bool) (j:ℕ) :
    j < 2 * n + 1 → 
    (int.of_nat n) * (int.of_nat (best_point n l)) -
            (2*(int.of_nat n) + 1) * (int.of_nat (count_tt (list.take (best_point n l) l)))
    ≥
    (int.of_nat n) * (int.of_nat j) -
            (2*(int.of_nat n) + 1) * (int.of_nat (count_tt (list.take j l)))
            :=
begin
    rw [best_point] ,
    intros ,
    have ineq : j ≤ (2*n) := begin
        rw <- nat.lt_succ_iff , assumption ,
    end,
    have h := func_argmax_ge (λ (i : ℕ),
                int.of_nat n * int.of_nat i - (2 * int.of_nat n + 1) * int.of_nat (count_tt (list.take i l)))
                (2*n) j ineq ,
    simp at h ,
    rw [add_comm] , assumption ,
end

theorem negate_rotation_lt : ∀ (n:ℕ) (i:ℕ) ,
    0 < n → negate_rotation n i < n :=
begin
    intros, rw [negate_rotation] ,
    split_ifs , assumption , apply nat.sub_lt_self , assumption ,
    cases i , contradiction ,
    have h : (nat.succ i = i + 1) := rfl ,
    rw h , linarith ,
end

theorem compose_rotation_lt : ∀ (n:ℕ) (i:ℕ) (j:ℕ) ,
    0 < n → compose_rotation n i j < n :=
begin
    intros , rw [compose_rotation] ,
    apply nat.mod_lt , assumption ,
end

theorem eq_0_of_dvd_of_lt : ∀ (n:ℕ) (m:ℕ) ,
    n < m → m ∣ n → n = 0 :=
begin
    intros , cases a_1 , cases a_1_w ,
    simp at a_1_h , assumption ,
    have h : (nat.succ a_1_w = a_1_w + 1) := rfl ,
    rw h at a_1_h ,
    have h2 : n > n := (
        calc n = m * (a_1_w + 1) : a_1_h
        ... = m * a_1_w + m*1 : by rw mul_add 
        ... = m * a_1_w + m : by simp
        ... ≥ m : by linarith
        ... > n : a),
    linarith ,
end

theorem eq_0_of_compose_negate : ∀ (n:ℕ) (i:ℕ) (j:ℕ) ,
    i < n →
    j < n → 
    compose_rotation n (negate_rotation n i) j = 0 →
    i = j :=
begin
    intros ,
    rw [negate_rotation] at a_2 ,
    rw [compose_rotation] at a_2 ,
    split_ifs at a_2 ,
    {
        simp at a_2 ,
        have h : (n ∣ j) := begin
            apply nat.dvd_of_mod_eq_zero , assumption ,
        end,
        subst i ,
        symmetry ,
        apply (eq_0_of_dvd_of_lt j n) , assumption, assumption ,
    },
    {
        have h : (n ∣ n - i + j) := begin
            apply nat.dvd_of_mod_eq_zero ,
            assumption ,
        end,
        clear a_2 , cases h ,
        cases h_w,
        {
            /- n - i + j = 0 case (find contradiction) -/
            have r : (n - i + j > n - i + j) := (
                calc n - i + j ≥ n - i + 0 : begin
                    apply nat.add_le_add_left , linarith
                end
                ... = n - i : by simp
                ... > 0: begin
                    apply nat.sub_pos_of_lt, assumption ,
                end
                ... = n * 0 : begin rw mul_zero,  end
                ... = n - i + j : by rw h_h
            ),
            linarith ,
        },
        cases h_w ,
        {
            /- n - i + j = n case (show i = j) -/
            rw [mul_one] at h_h ,
            have h2 : j + (n - i) = n := begin rw add_comm , assumption end,
            have h3 : (j + n) - i = n := begin rw nat.add_sub_assoc , assumption , apply le_of_lt , assumption, end,
            have h4 : (j + n) - i + i = n + i := by rw h3 ,
            have h5 : (j + n) - i + i = (n + j) := begin
                rw [nat.sub_add_cancel], rw [nat.add_comm], 
                linarith , 
            end,
            have h5 : n + i = n + j := begin
                rw <- h4 , rw <- h5 , 
            end,
            apply (@nat.add_left_cancel n i j) , assumption ,
        },
        {
            /- n - i + j ≥ 2*n case (find contradiction) -/
            have h2 : nat.succ (nat.succ h_w) = h_w + 2 := rfl ,
            have h3 : n - i ≤ n := begin
                    apply nat.sub_le_self ,
                end,
            rw h2 at * ,
            have h3 : n - i + j < n - i + j := (calc
                n - i + j ≤ n + j : by linarith
                ... < n + n : by linarith
                ... ≤ n * h_w + (n + n) : by linarith
                ... = n * (h_w + 2) : by ring
                ... = n - i + j : by rw h_h
            ),
            linarith
        }
    }
end

theorem compose_compose_rotation {α : Type} : ∀ (l:list α) (i:ℕ) (j:ℕ) ,
    i < list.length l →
    j < list.length l →
    list.drop i
        (list.drop j l ++ list.take j l) ++
      list.take i
        (list.drop j l ++ list.take j l) =
    list.drop (compose_rotation (list.length l) i j) l ++
    list.take (compose_rotation (list.length l) i j) l :=
begin
    intros ,
    rw <- list.rotate_eq_take_append_drop ,
    rw <- list.rotate_eq_take_append_drop ,
    rw <- list.rotate_eq_take_append_drop ,
    rw [compose_rotation] ,
    rw list.rotate_mod ,
    rw list.rotate_rotate , rw nat.add_comm ,
    apply le_of_lt , apply compose_rotation_lt ,
    linarith ,
    apply le_of_lt , assumption ,
    rw <- list.rotate_eq_take_append_drop ,
    rw list.length_rotate , apply le_of_lt, assumption ,
    apply le_of_lt, assumption,
end

theorem negate_negate_rotation {α : Type} : ∀ (l:list α) (i:ℕ) ,
    i < list.length l → 
    list.drop (negate_rotation (list.length l) i)
        (list.drop i l ++ list.take i l) ++
      list.take (negate_rotation (list.length l) i)
        (list.drop i l ++ list.take i l) =
    l :=
begin
    intros ,
    rw <- list.rotate_eq_take_append_drop ,
    rw <- list.rotate_eq_take_append_drop ,
    rw [negate_rotation] ,
    split_ifs ,
    {
        subst i , simp , 
    },
    {
        rw list.rotate_rotate , rw add_comm, rw nat.sub_add_cancel ,
        rw <- list.rotate_mod , simp , apply le_of_lt, assumption,
    },
    apply le_of_lt, assumption ,
    rw <- list.rotate_eq_take_append_drop ,
    apply le_of_lt , rw list.length_rotate ,
    apply negate_rotation_lt , linarith , apply le_of_lt, assumption,
end

theorem best_point_lt_length : ∀ (n : ℕ) (l : list bool) ,
    best_point n l < 1 + 2 * n :=
begin
    intros , rw [best_point] , rw (@nat.add_comm 1 (2*n)) ,
    apply argmax_lt_length ,
end

theorem take_app {α : Type} : ∀ (a : list α) (b : list α) ,
    list.take (list.length a) (a ++ b) = a :=
begin
    intros , rw list.take_append_of_le_length , rw list.take_all ,
    trivial ,
end

theorem count_tt_app : ∀ (a : list bool) (b : list bool) ,
    (count_tt (a ++ b)) = (count_tt a) + (count_tt b) :=
begin
    intros , induction a , simp [count_tt] ,
    cases a_hd ,
    simp [count_tt] , rw add_comm , assumption ,
    simp [count_tt] , rw a_ih , ring , 
end

theorem take_append_of_ge_length {α : Type} : ∀ (i : ℕ) 
    (a : list α) (b : list α) ,
    list.take (list.length a + i) (a ++ b) = a ++ list.take i b :=
begin
    intros, induction a, simp ,
    simp , rw (nat.add_comm 1) , rw <- nat.add_assoc , rw [list.take] ,
    rw nat.add_comm , rw a_ih , 
end

theorem count_tt_take_drop : ∀ (i:ℕ) (p:ℕ) (l:list bool) ,
    i + p < list.length l → 
    int.of_nat (count_tt (list.take i (list.drop p l ++ list.take p l))) =
    int.of_nat (count_tt (list.take (p+i) l)) -
        int.of_nat (count_tt (list.take p l)) :=
begin
    intros ,
    rw list.take_append_of_le_length ,
    have h : (
            int.of_nat (count_tt (list.take i (list.drop p l))) +
            int.of_nat (count_tt (list.take p l)) =
            int.of_nat (count_tt (list.take (p + i) l))) :=
        begin
            rw add_comm ,
            rw [<- int.of_nat_add] ,
            rw [<- count_tt_app] ,
            rw [<- take_append_of_ge_length] ,
            rw [list.take_append_drop] ,
            rw [list.length_take] ,
            rw [min_eq_left] ,
            linarith ,
        end,
    rw <- h , ring ,
    rw list.length_drop ,
    rw <- nat.add_le_to_le_sub ,
    apply le_of_lt , assumption , linarith ,
end

theorem count_tt_take_drop_2 : ∀ (i:ℕ) (p:ℕ) (l:list bool) ,
    p + i ≥ list.length l → 
    i ≤ list.length l →
    p ≤ list.length l →
    int.of_nat (count_tt (list.take i (list.drop p l ++ list.take p l))) =
        int.of_nat (count_tt l) -
        int.of_nat (count_tt (list.take p l)) +
        int.of_nat (count_tt (list.take (p+i-list.length l) l)) :=
begin
    intros ,
    have h : (i = list.length (list.drop p l) + (p+i-list.length l)) :=
        begin
            rw list.length_drop ,
            have h' : int.of_nat i = int.of_nat (list.length l - p + (p + i - list.length l)) := begin
                rw int.of_nat_add , rw int.of_nat_sub , rw int.of_nat_sub ,
                rw int.of_nat_add , ring , assumption , assumption ,
            end,
            simp at h' , simp , assumption ,
        end,
    have h2 := (calc
        int.of_nat (count_tt (list.take i (list.drop p l ++ list.take p l)))
        = 
        int.of_nat (count_tt (list.take (list.length (list.drop p l) + (p+i-list.length l)) (list.drop p l ++ list.take p l))) : by rw <- h
    ),
    rw h2, clear h2 , clear h ,
    rw take_append_of_ge_length ,
    rw list.take_take , rw min_eq_left ,
    rw count_tt_app , rw int.of_nat_add ,

    have q : int.of_nat (count_tt (list.drop p l)) =
    int.of_nat (count_tt l) - int.of_nat (count_tt (list.take p l)) :=
        begin
            have t :
                int.of_nat (count_tt (list.take p l)) + int.of_nat (count_tt (list.drop p l)) = int.of_nat (count_tt l) :=
                    begin
                        rw <- int.of_nat_add, rw <- count_tt_app ,
                        rw list.take_append_drop ,
                    end,
            rw <- t, ring ,
        end,

    rw q ,

    rw nat.sub_le_iff , rw (nat.add_comm p i) , rw nat.add_sub_cancel ,
    assumption ,
end

theorem mul_int_of_nat_1 : ∀ (a:ℤ) ,
    a * (int.of_nat 1) = a :=
begin
    have h : int.of_nat 1 = 1 := rfl ,
    intros , rw h , simp ,
end

/-
    This shows that given any path, we can rotate it to be a
    below_diagonal_path.
-/

theorem below_diagonal_path_rotate_best_point : ∀ (n : ℕ) (l : list bool) ,
    list.length l = 2*n + 1 →
    count_tt l = n →
    below_diagonal_path n (list.drop (best_point n l) l ++
                           list.take (best_point n l) l) :=
begin
    intros ,
    rw [below_diagonal_path] ,
    split ,
    {
        calc list.length (list.drop (best_point n l) l ++ list.take (best_point n l) l) =
        list.length (list.drop (best_point n l) l) + list.length (list.take (best_point n l) l) : by simp
        ... = list.length (list.take (best_point n l) l) + list.length (list.drop (best_point n l) l) : (by rw [nat.add_comm])
        ... = list.length (list.take (best_point n l) l ++ list.drop (best_point n l) l) :
            begin
                simp , rw min_eq_left , rw nat.sub_add_cancel ,
                apply le_of_lt , rw a , simp , apply best_point_lt_length ,
                apply le_of_lt , rw a , simp , apply best_point_lt_length ,
            end
        ... = list.length (l) : by rw list.take_append_drop
        ... = 2 * n + 1 : (by rw a)
    },
    split ,
    {
        calc count_tt (list.drop (best_point n l) l ++ list.take (best_point n l) l) =
        count_tt (list.drop (best_point n l) l) + count_tt (list.take (best_point n l) l) : by rw count_tt_app
        ... = count_tt (list.take (best_point n l) l) + count_tt (list.drop (best_point n l) l) : (by rw [nat.add_comm])
        ... = count_tt (list.take (best_point n l) l ++ list.drop (best_point n l) l) : by rw count_tt_app
        ... = count_tt (l) : by rw list.take_append_drop
        ... = n : (by rw a_1)
    },
    {
        intros ,

        have j' : (∃ j , j = best_point n l) , existsi (best_point n l), trivial, cases j', rename j'_w p, rename j'_h p_eq ,
        
        rw [<- p_eq] ,

        by_cases ((p+i) < 2*n + 1) ,
        {
            have ineq := best_point_gt n l (p + i) h,
            rw [<- p_eq] at ineq ,
            calc int.of_nat i * int.of_nat n -
                (2 * int.of_nat n + 1) * int.of_nat (count_tt
                (list.take i (list.drop p l ++ list.take p l)))
            = int.of_nat i * int.of_nat n -
                (2 * int.of_nat n + 1) * (
                    int.of_nat (count_tt (list.take (p + i) l)) -
                    int.of_nat (count_tt (list.take (p) l))
                ) :
                begin
                    rw count_tt_take_drop ,
                    rw [a, nat.add_comm] , assumption ,
                end
            ... =
            (int.of_nat n * int.of_nat (p + i) - (2 * int.of_nat n + 1) * int.of_nat (count_tt (list.take (p + i) l))) - 
            (int.of_nat n * int.of_nat p - (2 * int.of_nat n + 1) * int.of_nat (count_tt (list.take p l))) :
                begin
                    clear ineq,
                    simp [add_mul, int.of_nat_add, mul_add] ,
                    apply mul_comm ,
                end
            ... ≤ 0 :
                begin
                    linarith ,
                end
        },
        {
            have ineq := best_point_gt n l (p + i - (2*n+1))
                (begin
                    have h : (p < (2*n+1)) := begin
                        rw p_eq , simp , apply best_point_lt_length ,
                    end,
                    rw nat.sub_lt_left_iff_lt_add ,
                    linarith , linarith ,
                end),
            rw [<- p_eq] at ineq ,

            calc int.of_nat i * int.of_nat n - 
                (2 * int.of_nat n + 1) * int.of_nat (count_tt
                (list.take i (list.drop p l ++ list.take p l)))
            = int.of_nat i * int.of_nat n - 
                (2 * int.of_nat n + 1) * (
                    int.of_nat (count_tt l) -
                    int.of_nat (count_tt (list.take p l)) +
                    int.of_nat (count_tt (list.take (p+i-(2*n+1)) l))
                ) :
                begin
                    rw count_tt_take_drop_2 ,
                    rw a ,
                    linarith , linarith ,
                    rw a , simp , rw p_eq , apply le_of_lt ,
                    apply best_point_lt_length ,
                end
            ... =
            (int.of_nat n * int.of_nat (p + i - (2*n+1)) - (2 * int.of_nat n + 1) * int.of_nat (count_tt (list.take (p + i - (2*n+1)) l))) -
            (int.of_nat n * int.of_nat p - (2 * int.of_nat n + 1) * int.of_nat (count_tt (list.take p l))) :
                begin
                    clear ineq,
                    rw a_1 ,
                    rw int.of_nat_sub ,
                    simp [add_mul, int.of_nat_add, mul_add, mul_int_of_nat_1, int.of_nat_mul] ,
                    rw [int.mul_comm] ,
                    simp ,
                    rw (@int.mul_comm (int.of_nat n) (int.of_nat 2 * int.of_nat n)),
                    refl,
                    linarith ,
                end
            ... ≤ 0 :
                begin
                    linarith ,
                end
        }
    }

end

theorem le_add_cancel : ∀ (a:ℤ) (b:ℤ) (c:ℤ) ,
    a + c ≤ b + c → a ≤ b :=
    begin
        intros, linarith ,
    end

theorem a_plus_1_ge_a : ∀ (a:ℤ) ,
    a < a + 1 :=
    begin
        intros, linarith
    end

theorem nat_succ_a_le_b : ∀ (a b:ℕ) ,
    a < b → nat.succ a ≤ b:=
    begin
        intros a b h,
        have h: a + 1 ≤ b, from nat.succ_le_of_lt h,
        have h2: nat.succ a = a + 1 , from rfl,
        have h3: nat.succ a ≤ a + 1, from le_of_eq h2,
        exact le_trans h3 h
    end

theorem nat_le_of_int_le : ∀ (a:ℕ) (b:ℕ) ,
    int.of_nat a ≤ int.of_nat b → a ≤ b := begin
    intros a b h,
    induction a,
    {induction b, {trivial}, simp[int.of_nat_zero, int.of_nat_succ]},
    have hor: int.of_nat (nat.succ a_n) < int.of_nat b ∨ int.of_nat (nat.succ a_n) = int.of_nat b, 
        from lt_or_eq_of_le h,
    apply or.elim hor,
    {intro caseh, simp[int.of_nat_succ] at caseh, 
    have transh: int.of_nat a_n < int.of_nat a_n + 1, from a_plus_1_ge_a (int.of_nat a_n),
    have indh: int.of_nat a_n < int.of_nat b, from lt_trans transh caseh, 
    have h1: a_n ≤ b, from a_ih (le_of_lt indh),
    have hor: a_n < b ∨ a_n = b, from lt_or_eq_of_le h1,
    apply or.elim hor,
    {intro hor1, exact nat_succ_a_le_b a_n b hor1},
    intro hor,
    have nexth: int.of_nat a_n = int.of_nat b, from (congr_arg _) hor,
    have nothexth:  int.of_nat a_n ≠  int.of_nat b, from ne_of_lt indh,
    contradiction
    },
    intro caseh, rw h at *, have h1: nat.succ a_n = b, from int.no_confusion caseh id,
    apply le_of_eq h1
    end

theorem a_plus_a_plus_1_ge : ∀ (a:ℕ) (b:ℕ) ,
    a ≥ b → a + a + 1 ≥ b + b + 1 :=
    begin
        intros, linarith ,
    end

/-
    Given a below_diagonal_path, it must end in an `ff`
    (an edge going up) and the rest of it must be balanced.
-/

theorem below_diagonal_path_ends_in_ff_aux :
    ∀ (n : ℕ) (l : list bool) (d : ℕ) (j_tt : ℕ) (j_ff : ℕ) ,
    j_tt + j_ff + list.length l = 2*n + 1 →
    j_tt + count_tt l = n →
    j_tt = j_ff + d →
    ¬(l = list.nil) → 
    (forall (i:ℕ) , j_tt + j_ff ≤ i → i ≤ 2*n + 1 →
        ((int.of_nat i) * (int.of_nat n) -
            (2*(int.of_nat n)+1) * (int.of_nat (j_tt + count_tt (list.take (i - (j_tt + j_ff)) l))) ≤ 0)) →
    (exists t , l = t ++ [ff] ∧ balanced_aux t d)
| n [] d j_tt j_ff :=
    begin
        /- theorem only applies to non-empty lists -/
        intros , contradiction , 
    end
| n [ff] d j_tt j_ff :=
    begin
        /- list ends in ff: easy -/
        intros , existsi list.nil , split , simp , simp at a ,
        simp [count_tt] at a_1 , rw a_1 at * ,
        have h := (calc
            j_ff + (n+1) = n + (j_ff + 1) : by ring
            ... = 1 + 2 * n : by assumption
            ... = n + (n+1) : by ring
        ),
        have h2 : (j_ff = n) := add_right_cancel h ,
        rw h2 at * ,
        have h3 : (n + 0 = n + d) := calc n + 0 = n : by ring ... = n + d : by assumption ,
        have h4 : (0 = d) := add_left_cancel h3 ,
        rw <- h4 ,
        simp [balanced_aux] ,
    end
| n [tt] d j_tt j_ff :=
    begin
        /- list ends in tt: contradiction -/
        intros ,
        simp at a ,
        simp [count_tt] at a_1 ,
        have h := a_4 (j_tt + j_ff) (by linarith) (by linarith) ,
        simp at h , rw [count_tt] at h , simp at h ,
        have h2 : (j_tt + j_ff = 2*n) := add_right_cancel (calc
                j_tt + j_ff + 1 =
                j_tt + (j_ff + 1) : by simp 
                ... = 1 + 2 * n : by assumption
                ... = 2*n + 1 : by ring
            ),
        rw h2 at h ,
        rw <- a_1 at h ,
        simp [int.of_nat_mul, int.of_nat_add] at h ,
        simp [mul_add] at h ,
        linarith , 
    end
| n (ff :: (x::l)) 0 j_tt j_ff :=
    begin
        /- step up crossing the diagonal: contradiction -/
        intros ,
        /- substitute j_tt = j_ff -/
        simp at a_2 , rw a_2 at * ,
        /- the point (j_ff, j_ff + 1) is above the diagonal,
           that's where we derive the contradiction -/
        have h := a_4 (j_ff + j_ff + 1) (by linarith)
            (begin
                simp at a , linarith ,
            end),
        rwa (@nat.add_comm (j_ff + j_ff) 1) at h,
        rw nat.add_sub_cancel at h,
        simp [list.take, count_tt] at h,
        simp [int.of_nat_add, add_mul] at h,
        rw <- add_assoc at h ,
        /-have q : (2 * int.of_nat j_ff * int.of_nat n) = (int.of_nat j_ff * int.of_nat n) + (int.of_nat j_ff * int.of_nat n) := begin
             rw <- two_mul ,
            end,-/
        have r : int.of_nat 1 = 1 := rfl ,
        /-rw <- q at h ,-/
        rw r at  h,
        rw <- two_mul at h,
        simp at h,
        rw (mul_comm (int.of_nat j_ff) (int.of_nat n)) at h ,
        rw mul_assoc at h ,
        have h2 : int.of_nat n ≤ int.of_nat j_ff := le_add_cancel (int.of_nat n) (int.of_nat j_ff) (2 * (int.of_nat n * int.of_nat j_ff)) h ,
        have h3 : n ≤ j_ff := nat_le_of_int_le n j_ff h2 ,
        have h4 : 2*n + 1 > 2*n + 1 := (calc 
            2 * n + 1 = j_ff + j_ff + list.length (ff :: x :: l) : by rw a
            ... = j_ff + j_ff + 1 + 1 + list.length l : begin
                simp , rw <- add_assoc , simp ,
            end
            ... > j_ff + j_ff + 1 : by linarith
            ... ≥ n + n + 1 : a_plus_a_plus_1_ge j_ff n h3
            ... = 2*n + 1 : by rw two_mul
        ),
        linarith ,
    end
| n (ff :: (x::l)) (d+1) j_tt j_ff :=
    begin
        /- step up without crossing the diagonal -/
        intros ,
        have b1 : (j_tt + (j_ff + 1) + list.length (x :: l) = 2 * n + 1) := begin
            simp at a , simp , assumption ,
            end,
        have b2 : (j_tt + count_tt (x :: l) = n) := begin
            simp [count_tt] at a_1 , assumption ,
            end,
        have b3 : (j_tt = j_ff + 1 + d) := begin
            simp at a_2 , simp, assumption,
            end,
        have b4 : ¬(((x :: l) : list bool) = (list.nil : list bool)) := begin
            simp ,
            end,
        have b5 : ((∀ (i : ℕ),
            j_tt + (j_ff + 1) ≤ i →
            i ≤ 2 * n + 1 →
            int.of_nat i * int.of_nat n -
         (2 * int.of_nat n + 1) * int.of_nat (j_tt + count_tt (list.take (i - (j_tt + (j_ff + 1))) (x :: l))) ≤ 0)) :=
            begin
                intros ,
                have t := a_4 i (by linarith) (by linarith) ,
                have s : (i - (j_tt + (j_ff + 1))) + 1 = (i - (j_tt + j_ff)) := begin
                        rw <- (add_assoc j_tt) ,
                        rw <- nat.sub_sub ,
                        rw nat.sub_add_cancel ,
                        rw <- add_assoc at a_5 ,
                        rw add_comm at a_5 ,
                        rw nat.add_le_to_le_sub at a_5 ,
                        assumption , linarith ,
                    end ,
                rw <- s at t,
                rw [list.take] at t,
                assumption ,
            end,
        have ih := below_diagonal_path_ends_in_ff_aux n (x::l) d j_tt (j_ff + 1) b1 b2 b3 b4 b5,
        clear below_diagonal_path_ends_in_ff_aux b1 b2 b3 b4 b5 ,
        cases ih , rename ih_w l' , existsi ((ff :: l') : list bool) ,
        cases ih_h , split , rw ih_h_left ,
        simp ,
        rw [balanced_aux] , assumption ,
    end
| n (tt :: (x::l)) d j_tt j_ff :=
    begin
        intros ,
        have b1 : (j_tt + 1 + j_ff + list.length (x :: l) = 2 * n + 1) := begin
                simp , simp at a , assumption ,
            end ,
        have b2 : (j_tt + 1 + count_tt (x :: l) = n) :=
            begin
                simp [count_tt], simp [count_tt] at a_1 , assumption ,
            end,
        have b3 : (j_tt + 1 = j_ff + (d + 1)) :=
            begin
                rw a_2 , simp ,
            end ,
        have b4 : ¬(((x :: l) : list bool) = list.nil) :=
            begin
                simp ,
            end,
        have b5 : (∀ (i : ℕ),
            j_tt + 1 + j_ff ≤ i →
            i ≤ 2 * n + 1 →
            int.of_nat i * int.of_nat n -
            (2 * int.of_nat n + 1) * int.of_nat (j_tt + 1 + count_tt (list.take (i - (j_tt + 1 + j_ff)) (x :: l))) ≤
            0) :=
            begin
                intros ,
                have t := a_4 i (by linarith) (by linarith) ,
                have s : (i - (j_tt + (j_ff + 1))) + 1 = (i - (j_tt + j_ff)) := begin
                        rw <- (add_assoc j_tt) ,
                        rw <- nat.sub_sub ,
                        rw nat.sub_add_cancel ,
                        rw (add_comm j_tt 1) at a_5 ,
                        rw add_assoc at a_5 ,
                        rw nat.add_le_to_le_sub at a_5 ,
                        assumption , linarith ,
                    end ,
                rw <- s at t,
                rw [list.take] at t,
                rw [count_tt] at t,
                rw (add_assoc j_tt 1 j_ff) ,
                simp , simp at t ,
                assumption ,
            end ,
        have ih := below_diagonal_path_ends_in_ff_aux n (x::l) (d+1) (j_tt + 1) j_ff b1 b2 b3 b4 b5 , 
        clear below_diagonal_path_ends_in_ff_aux b1 b2 b3 b4 b5,
        cases ih ,
        rename ih_w l' ,
        existsi ((tt :: l') : list bool) ,
        cases ih_h, split,
        rw ih_h_left , simp ,
        rw [balanced_aux], assumption,
    end

theorem below_diagonal_path_ends_in_ff : ∀ (n : ℕ) (l : list bool) ,
    below_diagonal_path n l →
    (exists t , l = t ++ [ff] ∧ balanced t) :=
begin
    intros ,
    have h : (∃ (t : list bool), l = t ++ [ff] ∧ balanced_aux t 0) :=
    begin
        rw [below_diagonal_path] at a, cases a , cases a_right ,
        apply (below_diagonal_path_ends_in_ff_aux n l 0 0 0) ,
        simp , simp at a_left , assumption ,
        simp , assumption ,
        simp ,
        apply not.intro , intros , rw a at * , simp at a_left ,
        have h := (calc 0 = 1 + 2 * n : a_left ... > 0 : by linarith),
        linarith ,
        simp , simp at a_right_right , assumption ,
    end,
    cases h ,
    existsi h_w ,
    rw [balanced] , assumption ,
end

theorem count_tt_of_balanced_aux : ∀ (l : list bool) (d : ℕ) ,
    balanced_aux l d →
    count_tt l * 2 + d = list.length l
    | [] 0 :=
        begin
            intros , simp [count_tt] , 
        end
    | [] (d + 1) :=
        begin
            intros , simp [balanced_aux] at a , contradiction ,
        end
    | (tt :: l) d :=
        begin
            intros , simp [count_tt] ,
            rw add_mul , simp ,
            have h := count_tt_of_balanced_aux l (d+1) (begin
                    rw [balanced_aux] at a ,
                    assumption ,
                end),
            linarith ,
        end
    | (ff :: l) 0 :=
        begin
            intros , simp [balanced_aux] at a , contradiction ,
        end
    | (ff :: l) (d + 1) :=
        begin
            intros , simp [count_tt] ,
            have h := count_tt_of_balanced_aux l d (begin
                    rw [balanced_aux] at a ,
                    assumption ,
                end),
            linarith ,
        end

theorem count_tt_drop_of_balanced_aux : ∀ (l : list bool) (i : ℕ) (d : ℕ) ,
    balanced_aux l d →
    i ≤ list.length l →
    count_tt (list.drop i l) * 2 + i ≤ list.length l
    | [] i 0 :=
        begin
            intros , simp [list.drop, count_tt] , simp at a_1 ,
            assumption ,
        end
    | [] i (d + 1) :=
        begin
            intros , rw [balanced_aux] at a , contradiction ,
        end
    | (tt :: l) (i+1) d :=
        begin
            intros ,  rw [list.drop] , rw [list.length] ,
            rw <- add_assoc ,
            apply add_le_add_right , 
            apply (count_tt_drop_of_balanced_aux l i (d+1)) ,
            rw [balanced_aux] at a , assumption ,
            simp at a_1, linarith ,
        end
    | (ff :: l) i 0 :=
        begin
            intros, rw [balanced_aux] at a , contradiction ,
        end
    | (ff :: l) (i + 1) (d + 1) :=
        begin
            intros, rw [list.drop], rw [list.length] ,
            rw <- add_assoc ,
            apply add_le_add_right , 
            apply (count_tt_drop_of_balanced_aux l i d) ,
            rw [balanced_aux] at a , assumption ,
            simp at a_1, linarith ,
        end
    | l 0 d :=
        begin
            simp [list.drop] , intros ,
            have h := count_tt_of_balanced_aux l d a ,
            linarith ,
        end

theorem count_tt_drop_of_balanced : ∀ (l : list bool) (n : ℕ) (i : ℕ) ,
    balanced l →
    list.length l = 2 * n →
    i ≤ list.length l →
    count_tt (list.drop i l) * 2 + i ≤ 2 * n :=
begin
    intros ,
    rw <- a_1, 
    apply (count_tt_drop_of_balanced_aux l i 0) ,
    rw [balanced] at a, assumption ,
    assumption ,
end

theorem two_cancel : ∀ (n: ℕ) (m: ℕ),
    2*n = 2*m → n = m :=
begin
    intros ,
    have h : ((2*n) / 2) = ((2*m) / 2) := by rw a ,
    rw mul_comm at h , rw nat.mul_div_cancel at h ,
    rw mul_comm at h , rw nat.mul_div_cancel at h ,
    assumption, linarith , linarith ,
end

theorem count_tt_of_balanced : ∀ (l : list bool) (n : ℕ) ,
    balanced l → list.length l = 2 * n → count_tt l = n :=
begin
    intros ,
    rw [balanced] at a , 
    have h := count_tt_of_balanced_aux l 0 a,
    simp at h ,
    rw a_1 at h ,
    rw mul_comm at h ,
    exact two_cancel _ _ h ,
end

theorem count_tt_take_of_balanced : ∀ (l : list bool) (n : ℕ) (i : ℕ) ,
    balanced l →
    list.length l = 2 * n →
    i ≤ list.length l →
    count_tt (list.take i l) * 2 ≥ i :=
begin
    intros ,
    have h := count_tt_drop_of_balanced l n i a a_1 a_2 ,
    have j := count_tt_of_balanced l n a a_1 ,
    have q := (calc
        count_tt (list.take i l) + count_tt (list.drop i l) =
        count_tt (list.take i l ++ list.drop i l) : by rw count_tt_app
        ... = count_tt l : by rw list.take_append_drop
        ... = n : by rw j
    ),
    linarith ,
end

theorem le_of_double_le : ∀ (a:ℤ) ,
    2 * a ≤ 0 → a ≤ 0 := begin
    intros, linarith ,
end

theorem int_of_nat_ge : ∀ (a:ℕ) (b:ℕ) ,
    a ≥ b →
    int.of_nat a ≥ int.of_nat b :=
begin
    /- ugh, whatever -/
    intros, induction a, cases b , trivial ,
    have h : (nat.succ b = b + 1) := rfl ,
    rw h at * , linarith ,
    have q : (nat.succ a_n = a_n + 1) := rfl ,
    rw q at * ,
    by_cases (a_n + 1 = b) , rw h , linarith ,
    have r : (a_n ≥ b) := begin
        have s : (b < a_n + 1) := begin
            apply nat_lt_of_not_eq , apply nat.lt_succ_of_le ,
            assumption, apply not.intro , intros ,
            rw a at h , contradiction ,
        end,
        apply nat.le_of_lt_succ , assumption ,
    end,
    calc int.of_nat (a_n + 1)
        = int.of_nat a_n + int.of_nat 1 : by rw int.of_nat_add
    ... = int.of_nat a_n + 1 : rfl
    ... ≥ int.of_nat a_n : by linarith
    ... ≥ int.of_nat b : begin
            apply a_ih , assumption ,
        end
end 

theorem int_of_nat_ge_zero : ∀ (n:ℕ) ,
    int.of_nat n ≥ 0 :=
begin
    intros , trivial ,
end

theorem a_minus_b_minus_a_le_zero : ∀ (a:ℤ) (b:ℕ) ,
    a + (-int.of_nat b + -a) ≤ 0 :=
begin
    intros , simp ,
end

theorem a_minus_b_minus_times_c_le : ∀ (a:ℤ) (b:ℤ) (c:ℤ) (d:ℤ) ,
    b ≥ 0 →
    c ≥ d → 
    a - b * c ≤ a - b * d :=
begin
    intros ,
    have t : b*d ≤ b*c := begin
        apply mul_le_mul_of_nonneg_left , assumption, assumption ,
    end ,
    linarith ,
end

theorem two_n_plus_1_ge : ∀ (a:ℕ) ,
    2 * (int.of_nat a) + 1 ≥ 0 :=
begin
    intros ,
    have h : (int.of_nat a ≥ 0) := int_of_nat_ge_zero a ,
    linarith ,
end

/- Given a balanced string, we can append one `ff` (up-edge or
   parenthesis, depending on interpretation) and get a
   below_diagonal_path. -/

theorem below_diagonal_path_of_balanced : ∀ (n : ℕ) (l : list bool) ,
    list.length l = 2 * n →
    balanced l →
    below_diagonal_path n (l ++ [ff]) :=
begin
    intros , rw [below_diagonal_path] ,
    split,
    {
        simp , assumption ,
    },
    split ,
    {
        rw count_tt_app , simp [count_tt],
        apply count_tt_of_balanced , assumption, assumption,
    },
    {
        intros ,
        by_cases (i = 2*n + 1) ,
        {
            have h1 := (calc list.length (l ++ [ff]) = list.length l + 1 : by simp
            ... = 2*n + 1 :
                begin
                    rw a ,
                end
            ... = i :
                begin
                    rw h ,
                end),
            rw <- h1, rw list.take_all , rw h1 ,
            rw count_tt_app , simp [count_tt], 
            rw (count_tt_of_balanced l n) ,
            rw h,
            simp [int.of_nat_add, int.of_nat_mul] ,
            apply le_of_eq , refl ,
            assumption, assumption,
        },
        {
            have h1 := nat_lt_of_not_eq i (2*n+1) (by linarith) (by assumption) , clear a_2 h ,
            
            rw list.take_append_of_le_length ,
            have h2 := count_tt_take_of_balanced l n i a_1 a (begin
                    rw a , apply nat.le_of_lt_succ ,  assumption ,
                end),
            exact (le_of_double_le _ (calc
                2 * (int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * int.of_nat (count_tt (list.take i l)))
                =
                2 * int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * (2 * int.of_nat (count_tt (list.take i l))) : by ring
                ... =
                2 * int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * (int.of_nat 2 * int.of_nat (count_tt (list.take i l))) : rfl
                ... = 2 * int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * (int.of_nat (2 * count_tt (list.take i l))) :
                    begin
                        rw int.of_nat_mul ,
                    end
                ... ≤ 2 * int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * (int.of_nat i) :
                    begin
                        apply a_minus_b_minus_times_c_le,
                        apply two_n_plus_1_ge ,
                        apply int_of_nat_ge ,
                        rw mul_comm , assumption ,
                    end
                ... ≤ 0 :
                    begin
                        simp [add_mul] ,
                        rw mul_assoc ,
                        rw (mul_comm (int.of_nat i) (int.of_nat n)) ,
                        rw <- mul_assoc ,
                        simp ,
                        apply a_minus_b_minus_a_le_zero ,
                    end
            )) ,

            rw a , apply nat.le_of_lt_succ, assumption,
        }
    }
end

theorem eq_of_le_zero : ∀ (a:ℤ) (b:ℤ) ,
    a ≤ 0 → b ≤ 0 → (a+b) = 0 → a = 0 := begin intros, linarith, end

theorem gcd_2_n_plus_1 : ∀ (n:ℕ) ,
    nat.gcd (2*n + 1) n = 1 :=
begin
    intros , rw nat.gcd_comm , rw nat.gcd_rec , simp ,
    /- casework on n=0, n=1, or n=2 -/
    cases n ,
    simp ,
    cases n ,
    simp ,
    have h : (nat.succ (nat.succ n)) = n + 2 := rfl , rw h,
    rw nat.mod_eq_of_lt , simp , linarith ,
end

/-
    If one below_diagonal_path rotates to another, then the rotation
    must be 0. This ultimately shows that each orbit of path rotations 
    contains only one below_diagonal_path.
-/

theorem below_diagonal_rotation_is_0 : ∀ (n : ℕ) (l : list bool) (i : ℕ) ,
    i < (2*n + 1) →
    below_diagonal_path n l →
    below_diagonal_path n (list.drop i l ++ list.take i l) →
    i = 0 :=
begin
    intros ,
    rw [below_diagonal_path] at * ,
    cases a_1 ,
    cases a_1_right ,
    cases a_2 ,
    cases a_2_right ,
    have h1 := a_1_right_right i (begin
        apply le_of_lt , assumption ,
    end),
    have h2 := a_2_right_right ((2*n + 1) - i) (begin
        apply nat.sub_le_self ,
    end),
    clear a_1_right_right , clear a_2_right_right ,

    have f := (
        calc list.length (list.drop i l) = (list.length l - i) :
            by rw list.length_drop
         ... = 2*n + 1 - i :
            by rw a_1_left
    ),
    have e : ((list.take (2 * n + 1 - i) (list.drop i l ++ list.take i l))
        = list.drop i l) :=
        begin
            rw <- f ,
            apply take_app ,
        end,
    rw e at h2 ,
    have g := (calc
        int.of_nat (count_tt (list.drop i l)) = 
            int.of_nat (count_tt (list.take i l)) +
            int.of_nat (count_tt (list.drop i l)) -
            int.of_nat (count_tt (list.take i l)) : by ring
        ... = int.of_nat (count_tt (list.take i l) + count_tt (list.drop i l)) -
              int.of_nat (count_tt (list.take i l)) : by rw int.of_nat_add
        ... = int.of_nat (count_tt (list.take i l ++ list.drop i l)) -
              int.of_nat (count_tt (list.take i l)) : by rw count_tt_app
        ... = int.of_nat (count_tt l) -
              int.of_nat (count_tt (list.take i l)) : by rw list.take_append_drop
        ... = int.of_nat n - int.of_nat (count_tt (list.take i l)) : by rw a_1_right_left
    ),
    rw g at h2 ,

    /- replace int.of_nat (count_tt (list.take i l)) with x -/
    have j' : (∃ j , j = (count_tt (list.take i l))) , existsi (count_tt (list.take i l)), trivial, cases j', rename j'_w x ,
    rw <- j'_h at * ,

    have sum_eq_z := (calc
    (int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * int.of_nat x) +
    (int.of_nat (2 * n + 1 - i) * int.of_nat n - (2 * int.of_nat n + 1) * (int.of_nat n - int.of_nat x)) = 0 : begin
        have two_eq : 2 = int.of_nat 2 := by refl ,
        rw two_eq ,
        have one_eq : 1 = int.of_nat 1 := by refl ,
        rw one_eq ,
        simp [int.of_nat_mul, int.of_nat_add] ,
        rw int.of_nat_sub ,
        simp [int.of_nat_mul, int.of_nat_add] ,
        ring ,
        apply le_of_lt, rw add_comm, assumption,
    end),

    have eq_z := (eq_of_le_zero 
        (int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * int.of_nat x)
    (int.of_nat (2 * n + 1 - i) * int.of_nat n - (2 * int.of_nat n + 1) * (int.of_nat n - int.of_nat x)) h1 h2 sum_eq_z) ,

    have t := (calc
        int.of_nat i * int.of_nat n
            = int.of_nat i * int.of_nat n - 0 : by ring
        ... = int.of_nat i * int.of_nat n -
        (int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * int.of_nat x) : by rw eq_z
        ... = (2*int.of_nat n+1) * int.of_nat x : by ring
    ),
    have t' : (int.of_nat (i * n) = int.of_nat ((2 * n + 1) * x)) :=
        begin
            simp [int.of_nat_add, int.of_nat_mul] ,
            have one' : (int.of_nat 1 = 1) := rfl ,
            have two' : (int.of_nat 2 = 2) := rfl ,
            rw one', rw two',
            simp at t , assumption ,
        end,
    have u : i * n = (2 * n + 1) * x := begin
            simp at t' , simp, assumption,
        end ,
    have gcd1 : (nat.gcd (2 * n + 1) n = 1) := gcd_2_n_plus_1 n,
    have div0: (2 * n + 1) ∣ (2 * n + 1) * x := begin
        apply dvd_mul_right ,
    end, 
    have div1 : (2 * n + 1) ∣ (i * n) := begin
        rw <- u at div0 , assumption ,
    end ,
    have div2 : (2*n + 1) ∣ i :=
        begin
            apply (@nat.coprime.dvd_of_dvd_mul_right i n) ,
            rw [nat.coprime] , assumption , assumption ,
        end,
    have i_eq_0 : (i = 0) := begin
        cases div2 , cases div2_w , simp at div2_h , assumption ,
        have i_gt_i : (i > i) :=
            (calc i = (2 * n + 1) * nat.succ div2_w : div2_h
               ... = (2 * n + 1) * (div2_w + 1) : by refl
               ... = (2 * n + 1) * (1 + div2_w) : by rw [@nat.add_comm 1]
               ... = (2 * n + 1) * 1 + (2 * n + 1) * div2_w : by rw mul_add
               ... = (2 * n + 1) + (2 * n + 1) * div2_w : by simp
               ... ≥ (2 * n + 1) : by linarith
               ... > i : by assumption
            ),
        linarith ,
    end,
    assumption ,
end

theorem below_diagonal_rotations_eq : ∀ (n : ℕ) (l : list bool) (l' : list bool) (i : ℕ) (i' : ℕ) ,
    below_diagonal_path n l →
    below_diagonal_path n l' →
    i < 1 + 2 * n → 
    i' < 1 + 2 * n → 
    list.drop i l ++ list.take i l = list.drop i' l' ++ list.take i' l' → 
    l = l' ∧ i = i' :=
begin
    intros ,
    have e := (calc
        l = 
            list.drop (negate_rotation (1+2*n) i)
                (list.drop i l ++ list.take i l) ++
            list.take (negate_rotation (1+2*n) i)
                (list.drop i l ++ list.take i l) : by
                begin
                    rw [below_diagonal_path] at a ,
                    cases a ,
                    rw nat.add_comm at a_left ,
                    rw <- a_left ,
                    rw [negate_negate_rotation] ,
                    rw a_left , assumption ,
                end
        ... = 
            list.drop (negate_rotation (1+2*n) i)
                (list.drop i' l' ++ list.take i' l') ++
            list.take (negate_rotation (1+2*n) i)
                (list.drop i' l' ++ list.take i' l') : by rw a_4
        ... =
            list.drop (compose_rotation (1+2*n) (negate_rotation (1+2*n) i) i') l'
            ++
            list.take (compose_rotation (1+2*n) (negate_rotation (1+2*n) i) i') l' : by
            begin
                rw [below_diagonal_path] at a_1 ,
                cases a_1 ,
                rw nat.add_comm at a_1_left ,
                rw <- a_1_left ,
                rw [compose_compose_rotation] ,
                apply negate_rotation_lt ,
                rw a_1_left , linarith ,
                rw a_1_left , assumption ,
            end
        ) ,
    have h : ((compose_rotation (1 + 2 * n) (negate_rotation (1 + 2 * n) i) i') = 0)
        :=
        (begin
            apply (below_diagonal_rotation_is_0 n l' _) ,
            rw nat.add_comm ,
            apply compose_rotation_lt , linarith ,
            assumption ,
            rw [<- e] , assumption ,
        end),
    rw h at e ,
    rw [list.drop, list.take] at e , simp at e ,
    split ,
    {
        assumption ,
    },
    {
        apply (eq_0_of_compose_negate (1+2*n)) ,
        assumption, assumption, assumption ,
    },
end

/-
    set of `below_diagonal_path n` strings has cardinality
    `catalan n`. This is done with the correspondence between
    balanced parentheses strings and below_diagonal_paths.
-/

theorem has_card_set_below_diagonal_path_catalan : ∀ n ,
    has_card {l : list bool | below_diagonal_path n l} (catalan n) :=
begin
    intros ,
    apply (card_bijection (set_balanced n) _
        (catalan n)
        (λ l , l ++ [ff])) ,
    {
        rw set_balanced , simp , intros ,
        apply below_diagonal_path_of_balanced , assumption , assumption ,
    },
    {
        simp , intros ,
        existsi (list.take (2*n) y) ,
        have h := below_diagonal_path_ends_in_ff n y a ,
        cases h , cases h_h ,
        have e := (
            calc list.length h_w = list.length (h_w ++ [ff]) - list.length [ff] : 
                by simp 
            ... = list.length y - list.length [ff] : by subst y
            ... = list.length y - 1 : by simp
            ... = (2*n + 1) - 1 : (begin
                rw below_diagonal_path at * ,
                cases a, 
                rw a_left ,
            end)
            ... = (2 * n) : by simp
        ),
        have e2 := (
            calc list.take (2 * n) y = list.take (list.length h_w) y : by rw e
            ... = list.take (list.length h_w) (h_w ++ [ff]) : by subst y
            ... = h_w : by rw take_app
        ),
        rw e2 ,
        split , rw [set_balanced] , simp , split , assumption, assumption ,
        subst y ,
    },
    {
        rw set_balanced , simp , intros ,
        calc x = list.take (list.length x) (x ++ [ff]) : by rw take_app
        ... = list.take (list.length x') (x' ++ [ff]) : by rw [a, a_2, a_4]
        ... = x' : by rw take_app
    },
    {
        apply has_card_set_balanced
    },
end

/-
    Shows that all the rotations of all the below_diagonal_path
    strings are all unique and make up all paths. 
-/

theorem has_card_set_n_choose_k_catalan : ∀ n ,
    has_card (set_n_choose_k (2*n+1) n) (catalan n * (2*n+1)) :=
begin
    intros ,
    apply (card_product_nat
        {l : list bool | below_diagonal_path n l}
        (2*n + 1)
        (set_n_choose_k (2*n+1) n)
        (catalan n)
        (λ l , λ i , list.drop i l ++ list.take i l)
    ) ,
    {
        rw set_n_choose_k , simp , intros ,
        split ,
        rw below_diagonal_path at * , cases a ,
        rw a_left ,
        have e : min y (2 * n + 1) = y :=
            (begin
                apply min_eq_left , apply le_of_lt , rw nat.add_comm , assumption ,
            end),
        {
            calc 2 * n + 1 - y + min y (2 * n + 1) = 2 * n + 1 - y + y : by rw e
            ... = 2 * n + 1 :
                begin
                    rw nat.sub_add_cancel , apply le_of_lt , rw add_comm,
                    assumption, 
                end
            ... = 1 + 2 * n : by apply nat.add_comm
        },
        {
            rw below_diagonal_path at a , cases a , cases a_right ,
            calc count_tt (list.drop y x ++ list.take y x)
                = count_tt (list.drop y x) + count_tt (list.take y x) : by rw count_tt_app
            ... = count_tt (list.take y x) + count_tt (list.drop y x) : by rw nat.add_comm
            ... = count_tt (list.take y x ++ list.drop y x) : by rw count_tt_app
            ... = count_tt x : by rw list.take_append_drop
            ... = n : by rw a_right_left
        },
    },
    {
        intros ,
        rw set_n_choose_k at * ,
        simp at a ,
        cases a ,
        simp ,
        existsi (list.drop (best_point n z) z ++ list.take (best_point n z) z) ,
        split ,
        {
            apply below_diagonal_path_rotate_best_point ,
            rw nat.add_comm , assumption ,
            assumption ,
        },
        existsi (negate_rotation (1+2*n) (best_point n z)) ,
        split ,
        {
            apply negate_rotation_lt , linarith ,
        },
        {
            rw [<- a_left] ,
            apply negate_negate_rotation ,
            rw a_left ,
            apply best_point_lt_length ,
        },
    },
    {
        simp , intros ,
        apply (below_diagonal_rotations_eq n x x' y y') ; assumption ,
    },
    {
        apply has_card_set_below_diagonal_path_catalan ,
    },
end

/- Our main theorem -/

theorem catalan_identity : ∀ (n:ℕ) ,
    catalan n * (2*n+1) = choose (2*n + 1) n :=
begin
    intros ,
    have h : has_card (set_n_choose_k (2*n+1) n) (catalan n * (2*n+1)) :=
        has_card_set_n_choose_k_catalan n,
    have i : has_card (set_n_choose_k (2*n+1) n) (choose (2*n+1) n) :=
        has_card_set_n_choose_k (2*n+1) n ,
    apply cardinality_unique (set_n_choose_k (2*n+1) n) _ _ ,
    assumption, assumption ,
end
