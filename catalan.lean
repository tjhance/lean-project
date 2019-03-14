import project.identities
import tactic.linarith

def balanced_aux : (list bool) → (ℕ) → Prop
    | [] 0 := true
    | [] (d + 1) := false
    | (tt :: l) d := balanced_aux l (d + 1)
    | (ff :: l) 0 := false
    | (ff :: l) (d + 1) := balanced_aux l d

def balanced (l : list bool) : Prop := balanced_aux l 0

def set_balanced (n : ℕ) : set (list bool) :=
    { l : list bool | list.length l = 2 * n ∧ balanced l }

def sum_to : (ℕ) → (ℕ → ℕ) → ℕ
    | 0 f := 0
    | (n+1) f := f n + sum_to n f

def catalan_aux : ℕ → ℕ → ℕ
    | b 0 := 1
    | 0 (n + 1) := 1 /- doesn't matter -/
    | (b + 1) (n + 1) := sum_to (n+1) (λ i,
        catalan_aux b i * catalan_aux b (n-i))
def catalan (n : ℕ) : ℕ :=
    catalan_aux n n

theorem catalan_recurrence : ∀ n ,
    catalan (n+1) = sum_to (n+1) (λ i , catalan i * catalan (n - i)) :=
    sorry

theorem balanced_recursor : ∀ (l : list bool) ,
    balanced l ↔ (∃ a b , balanced a ∧ balanced b ∧ l = tt :: a ++ ff :: b) :=
    sorry

/- split (A)B into A, B -/
def split_parens_aux : (list bool) → (ℕ) → (list bool × list bool)
| ([]) n := ([],[])
| (ff :: l) 0 := ⟨ [], [] ⟩ /- doesn't matter -/
| (ff :: l) 1 := ⟨ [], l ⟩
| (ff :: l) (d + 1) := let p := split_parens_aux l d in ⟨ ff :: p.1 , p.2 ⟩
| (tt :: l) (d) := let p := split_parens_aux l (d+1) in ⟨ tt :: p.1 , p.2 ⟩
def split_parens : (list bool) → (list bool × list bool)
| [] := ([],[]) /- doesn't matter -/
| (ff :: l) = split_parens_aux l 1
| (tt :: l) = ([],[]) /- doesn't matter -/

/- combined A, B into (A)B -/
def combine_parens (l : list bool) (m : list bool) : (list bool) :=
    tt :: l ++ ff :: m

theorem balanced_split_parens_1 : ∀ (l : list bool) ,
    balanced l -> balanced (split_parens l).1 := sorry

theorem balanced_split_parens_2 : ∀ (l : list bool) ,
    balanced l -> balanced (split_parens l).2 := sorry

theorem balanced_combine : ∀ (l : list bool) (m : list bool) ,
    balanced l →
    balanced m →
    balanced (combine_parens l m) := sorry

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
    := sorry

theorem even_length_of_balanced : ∀ (l : list bool) ,
    balanced l →
    2 ∣ list.length l
    := sorry

theorem length_split_parens_1_le : ∀ (l : list bool) ,
    balanced l →
    ¬(l = list.nil) →
    list.length (split_parens l).1 ≤ list.length l - 2

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
                    exact sorry ,
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

theorem even_nat_lt : ∀ (n:ℕ) (m:ℕ) ,
    (n) < 2*(m + 1) → 
    ¬ ((n) = 2*m) →
    2 ∣ n → 
    n < 2*m := sorry

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
        rw [catalan_aux] ,
        apply (card_1 _ []) ,
        simp ,
        intros , simp at a_1 , cases a_1 , cases y ; trivial ,
    end
| (bound+1) (n+1) :=
    begin
        intros , 
        rw catalan_recurrence ,
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
        have e : (sum_to (n + 1) = sum_to j) , rw j'_h, rw e , clear e,
        have n_bound : (n+1) < (bound+1) := a , /- copy this -/
        rw [<- j'_h] at a ,
        clear j'_h ,

        /- do induction on j for the summation of the recursion -/
        induction j, 
        {
            rw [sum_to] ,
            apply catalan_set_base ,
        },
        {
            rw [sum_to] ,
            rw [@nat.add_comm (catalan j_n * catalan (n - j_n)) _] ,
            apply catalan_set_induction ,
            {
                apply j_ih ,
                calc j_n < bound + 1 : sorry , /- should be easy -/
            },
            {
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
                    simp, intros ,
                    existsi (split_parens z).1 ,
                    existsi (split_parens z).2 ,
                    apply combine_parens_split_parens ,
                    assumption ,
                    apply not.intro , intros , subst z , simp at a_1 ,linarith , 
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
                                rw a_9 ,
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