import project.identities
import tactic.linarith
import data.list
import data.int.basic
import data.nat.gcd

/-
    Catalan numbers.

    First we define
    `balanced`: balanced strength of parentheses (`tt` is an 
    open paren, `ff` is a close paren).

    We define `catalan` by recurence, then show that `catalan n`
    is the cardinality of the set of balanced strings of length 2n.
    (theorem `has_card_set_balanced`)

    Then by doing a bijection through paths from (0,0) to (n,n+1),
    we prove our main result, the theorem
    `catalan_identity`.
-/

def balanced_aux : (list bool) → (ℕ) → Prop
    | [] 0 := true
    | [] (d + 1) := false
    | (tt :: l) d := balanced_aux l (d + 1)
    | (ff :: l) 0 := false
    | (ff :: l) (d + 1) := balanced_aux l d

def balanced (l : list bool) : Prop := balanced_aux l 0

def set_balanced (n : ℕ) : set (list bool) :=
    { l : list bool | list.length l = 2 * n ∧ balanced l }

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

theorem split_parens_combine_parens : ∀ (l : list bool) (m : list bool) ,
    balanced l →
    balanced m →
    split_parens (combine_parens l m) = ⟨l, m⟩ := sorry

theorem combine_parens_split_parens : ∀ (l : list bool) ,
    balanced l →
    ¬(l = list.nil) → 
    combine_parens (split_parens l).1 (split_parens l).2 = l := sorry

theorem length_combine_parens : ∀ (l : list bool) (m : list bool) ,
    balanced l →
    balanced m →
    list.length (combine_parens l m) = list.length l + list.length m + 2
    :=
begin
    intros , rw [combine_parens] , simp , rw [<- add_assoc] , simp ,
end

/- why can't I find these theorems anywhere wtf? -/
theorem eq_zero_of_le : ∀ (a:ℕ) (b:ℕ) ,
    a ≤ b → a-b = 0 :=
begin intros,
calc a-b = a - (min a b) : by rw nat.sub_min
    ... = a - a : by simp[min, *]
    ... = 0 : by simp
end

theorem nat_mul_sub : ∀ (n:ℕ) (a:ℕ) (b:ℕ) ,
    n*(a-b) = n*a - n*b :=
begin  
    intros ,
    by_cases (b ≤ a) ,
    {
        have h : (a-b+b = a) :=
            begin
                rw add_comm ,
                apply nat.add_sub_cancel' , assumption ,
            end,
        calc n*(a-b)
            = n*(a-b) + n*b - n*b : by rw nat.add_sub_cancel
        ... = n*(a-b+b) - n*b : by rw mul_add
        ... = n*a - n*b : by rw h
    },
    {
        have i : b > a := sorry ,
        have h : (a-b) = 0 := begin
            apply eq_zero_of_le , apply le_of_lt , assumption ,
        end,
        have j : n*b ≥ n*a := sorry ,
        have k : (n*a - n*b) = 0 := begin
            apply eq_zero_of_le , assumption ,
        end,
        rw [h, k] , simp , 
    },
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
    ... = 2 * ((n+1) - (a+1)) : by rw [nat_mul_sub 2 (n+1) (a+1)]
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

lemma has_card_set_balanced_aux : ∀ bound n ,
    n < bound →
    has_card (set_balanced n) (catalan n)
| 0 n := sorry
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
                            rw [mul_add] ,
                            exact sorry
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
                     exact sorry /- should be easy -/
                 },
                 {
                     apply (has_card_set_balanced_aux bound) ,
                     exact sorry /- should be easy -/
                 },
            }
        }

    end

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

def best_point (n:ℕ) (l : list bool) :=
    argmax (λ i ,
        (int.of_nat n) * (int.of_nat i) -
            (2*(int.of_nat n) + 1) * (int.of_nat (count_tt (list.take i l)))
    ) (2*n)

def negate_rotation (n:ℕ) (i:ℕ) :=
    if i = 0 then 0 else n - i

def compose_rotation (n:ℕ) (i:ℕ) (j:ℕ) :=
    (i + j) % n

theorem best_point_gt (n:ℕ) (l : list bool) (j:ℕ) :
    j < 2 * n + 1 → 
    (int.of_nat n) * (int.of_nat (best_point n l)) -
            (2*(int.of_nat n) + 1) * (int.of_nat (count_tt (list.take (best_point n l) l)))
    ≥
    (int.of_nat n) * (int.of_nat j) -
            (2*(int.of_nat n) + 1) * (int.of_nat (count_tt (list.take j l)))
            := sorry

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
        exact sorry
    }
end

theorem compose_compose_rotation {α : Type} : ∀ (l:list α) (i:ℕ) (j:ℕ) ,
    i < list.length l → 
    list.drop i
        (list.drop j l ++ list.take j l) ++
      list.take i
        (list.drop j l ++ list.take j l) =
    list.drop (compose_rotation (list.length l) i j) l ++
    list.take (compose_rotation (list.length l) i j) l := sorry

theorem negate_negate_rotation {α : Type} : ∀ (l:list α) (i:ℕ) ,
    i < list.length l → 
    list.drop (negate_rotation (list.length l) i)
        (list.drop i l ++ list.take i l) ++
      list.take (negate_rotation (list.length l) i)
        (list.drop i l ++ list.take i l) =
    l := sorry

theorem best_point_lt_length : ∀ (n : ℕ) (l : list bool) ,
    best_point n l < 1 + 2 * n := sorry

theorem count_tt_take_drop : ∀ (i:ℕ) (p:ℕ) (l:list bool) ,
    i + p < list.length l → 
    int.of_nat (count_tt (list.take i (list.drop p l ++ list.take p l))) =
    int.of_nat (count_tt (list.take (p+i) l)) -
        int.of_nat (count_tt (list.take p l)) := sorry

theorem count_tt_take_drop_2 : ∀ (i:ℕ) (p:ℕ) (l:list bool) ,
    p + i ≥ list.length l → 
    int.of_nat (count_tt (list.take i (list.drop p l ++ list.take p l))) =
        int.of_nat (count_tt l) -
        int.of_nat (count_tt (list.take p l)) +
        int.of_nat (count_tt (list.take (p+i-list.length l) l)) := sorry

theorem int_of_nat_add : ∀ (a:ℕ) (b:ℕ) ,
    int.of_nat (a + b) = int.of_nat a + int.of_nat b := sorry

theorem int_of_nat_sub : ∀ (a:ℕ) (b:ℕ) ,
    b ≤ a →
    int.of_nat (a - b) = int.of_nat a - int.of_nat b := sorry

theorem int_of_nat_mul : ∀ (a:ℕ) (b:ℕ) ,
    int.of_nat (a * b) = int.of_nat a * int.of_nat b := sorry

theorem mul_int_of_nat_1 : ∀ (a:ℤ) ,
    a * (int.of_nat 1) = a := sorry

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
        ... = list.length (list.take (best_point n l) l ++ list.drop (best_point n l) l) : sorry
        ... = list.length (l) : sorry
        ... = 2 * n + 1 : (by rw a)
    },
    split ,
    {
        calc count_tt (list.drop (best_point n l) l ++ list.take (best_point n l) l) =
        count_tt (list.drop (best_point n l) l) + count_tt (list.take (best_point n l) l) : sorry
        ... = count_tt (list.take (best_point n l) l) + count_tt (list.drop (best_point n l) l) : (by rw [nat.add_comm])
        ... = count_tt (list.take (best_point n l) l ++ list.drop (best_point n l) l) : sorry
        ... = count_tt (l) : sorry
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
                    simp [add_mul, int_of_nat_add, mul_add] ,
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
                    exact sorry
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
                    linarith ,
                end
            ... =
            (int.of_nat n * int.of_nat (p + i - (2*n+1)) - (2 * int.of_nat n + 1) * int.of_nat (count_tt (list.take (p + i - (2*n+1)) l))) -
            (int.of_nat n * int.of_nat p - (2 * int.of_nat n + 1) * int.of_nat (count_tt (list.take p l))) :
                begin
                    clear ineq,
                    rw a_1 ,
                    rw int_of_nat_sub ,
                    simp [add_mul, int_of_nat_add, mul_add, mul_int_of_nat_1, int_of_nat_mul] ,
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

theorem below_diagonal_path_ends_in_ff : ∀ (n : ℕ) (l : list bool) ,
    below_diagonal_path n l →
    (exists t , l = t ++ [ff] ∧ balanced t) := sorry

theorem below_diagonal_path_of_balanced : ∀ (n : ℕ) (l : list bool) ,
    list.length l = 2 * n →
    balanced l →
    below_diagonal_path n (l ++ [ff]) := sorry

theorem take_app {α : Type} : ∀ (a : list α) (b : list α) ,
    list.take (list.length a) (a ++ b) = a := sorry

theorem count_tt_app : ∀ (a : list bool) (b : list bool) ,
    (count_tt (a ++ b)) = (count_tt a) + (count_tt b) := sorry

theorem eq_of_le_zero : ∀ (a:ℤ) (b:ℤ) ,
    a ≤ 0 → b ≤ 0 → (a+b) = 0 → a = 0 := sorry

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
        exact sorry /- should be easy -/
    end),
    clear a_1_right_right , clear a_2_right_right ,

    have f := (
        calc list.length (list.drop i l) = (list.length l - i) : sorry
         ... = 2*n + 1 - i : sorry
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
            int.of_nat (count_tt (list.take i l)) : sorry
        ... = int.of_nat (count_tt (list.take i l) + count_tt (list.drop i l)) -
              int.of_nat (count_tt (list.take i l)) : sorry
        ... = int.of_nat (count_tt (list.take i l ++ list.drop i l)) -
              int.of_nat (count_tt (list.take i l)) : sorry
        ... = int.of_nat (count_tt l) -
              int.of_nat (count_tt (list.take i l)) : sorry
        ... = int.of_nat n - int.of_nat (count_tt (list.take i l)) : sorry
    ),
    rw g at h2 ,

    /- replace int.of_nat (count_tt (list.take i l)) with x -/
    have j' : (∃ j , j = (count_tt (list.take i l))) , existsi (count_tt (list.take i l)), trivial, cases j', rename j'_w x ,
    rw <- j'_h at * ,

    have sum_eq_z := (calc
    (int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * int.of_nat x) +
    (int.of_nat (2 * n + 1 - i) * int.of_nat n - (2 * int.of_nat n + 1) * (int.of_nat n - int.of_nat x)) = 0 : sorry),

    have eq_z := (eq_of_le_zero 
        (int.of_nat i * int.of_nat n - (2 * int.of_nat n + 1) * int.of_nat x)
    (int.of_nat (2 * n + 1 - i) * int.of_nat n - (2 * int.of_nat n + 1) * (int.of_nat n - int.of_nat x)) h1 h2 sum_eq_z) ,

    have t := (calc
        i * n = (2*n+1) * x : sorry
    ),
    have gcd1 : (nat.gcd n (2*n+1) = 1) := sorry,
    have div1 : (2*n + 1) ∣ (i * n) := sorry,
    have div2 : (2*n + 1) ∣ i := sorry,
    have i_eq_0 : (i = 0) := sorry,
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
            ... = 2 * n + 1 : sorry
            ... = 1 + 2 * n : by apply nat.add_comm
        },
        {
            rw below_diagonal_path at a , cases a , cases a_right ,
            calc count_tt (list.drop y x ++ list.take y x)
                = count_tt (list.drop y x) + count_tt (list.take y x) : by rw count_tt_app
            ... = count_tt (list.take y x) + count_tt (list.drop y x) : by rw nat.add_comm
            ... = count_tt (list.take y x ++ list.drop y x) : by rw count_tt_app
            ... = count_tt x : sorry
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
