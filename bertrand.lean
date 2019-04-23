import data.nat.choose
import data.nat.prime
import data.nat.gcd
import tactic.linarith

open classical

/-
    https://en.wikipedia.org/wiki/Proof_of_Bertrand%27s_postulate
-/

/- "lemma 1" -/

lemma four_n_bound : ∀ (n : ℕ) ,
    4 ^ n ≤ 2 * n * (choose (2*n) n) := sorry

/- "lemma 2" -/

lemma p_to_R_bound : ∀ (p:ℕ) (r:ℕ) (n:ℕ) ,
    nat.prime p →
    p ^ r ∣ (choose (2*n) n) →
    p ^ r ≤ 2*n := sorry

/- "lemma 3" -/

lemma central_primes_do_not_divide : ∀ (p n : ℕ) ,
    nat.prime p →
    p ≠ 2 →
    2*n / 3 < p →
    p ≤ n →
    ¬ (p ∣ (choose (2*n) n)) := sorry

/- range-related lemmas -/

def range_to (n:ℕ) (m:ℕ) := list.range' n (m-n+1)

theorem range_to_append : ∀ (n m k : ℕ) ,
    n ≤ m → m ≤ k →
    range_to n m ++ range_to (m+1) k = range_to n k := sorry

/- "lemma 4" -/

def primorial (n : ℕ) : ℕ :=
    (list.filter nat.prime (range_to 1 n)).prod

lemma primorial_ratio_eq_prod : ∀ (n m : ℕ) ,
    m ≤ n →
    primorial n / primorial m =
        (list.filter nat.prime (range_to (m+1) n)).prod := sorry

lemma prime_list_dvd : ∀ (n m k : ℕ) ,
    (∀ (p:ℕ) , nat.prime p → m+1 ≤ p → p ≤ n → p ∣ k) → 
    (list.filter nat.prime (range_to (m+1) n)).prod ∣ k := sorry

lemma p_dvd_choose_2m_plus_1_of_ge_m_plus_2 : ∀ (m p : ℕ) ,
    nat.prime p →
    m + 2 ≤ p →
    p ≤ 2*m + 1 →
    p ∣ choose (2*m+1) (m+1) := sorry

lemma primorial_ratio_le_choose : ∀ (m : ℕ) ,
    m ≥ 2 →
    primorial (2*m + 1) / primorial (m+1) ≤ (choose (2*m + 1) (m+1)) := sorry

lemma primorial_2m_plus_1_le_choose : ∀ (m : ℕ) ,
    m ≥ 2 →
    primorial (2*m + 1) ≤ primorial (m+1) * (choose (2*m + 1) (m+1)) := sorry

lemma choose_2m_plus_1_le_power_2 : ∀ (m : ℕ) ,
    choose (2*m + 1) (m+1) ≤ 2^(2*m) := sorry

lemma primorial_2m_plus_1_le_power_2 : ∀ (m : ℕ) ,
    m ≥ 2 →
    primorial (2*m + 1) ≤ primorial (m+1) * 2^(2*m) := sorry

lemma case_by_parity : ∀ (n : ℕ) ,
    (∃ (m:ℕ) , n = 2*m) ∨ (∃ (m:ℕ) , n = 2*m + 1) := sorry

lemma le_2_pow_2_mul_2_mul_plus_1 : ∀ (m : ℕ) ,
    2 ^ (2 * (2 * m + 1)) ≤ 2 ^ (2 * (2 * (m + 1))) := sorry

lemma primorial_bound : ∀ (n : ℕ) ,
    n ≥ 3 →
    8 * primorial n < 2 ^ (2*n)
| 0 := sorry
| 1 := sorry
| 2 := sorry
| 3 := sorry
| 4 := sorry
| (n+5) := begin
    intros ,
    cases (case_by_parity (n+5)) ,
    {
        cases h , rename h_w m , rw h_h at * ,
        cases m , simp at a , linarith ,
        have q : (nat.succ m) = (m+1) := rfl , rw q at * , clear q ,
        have m_ge_1 : m ≥ 1 := sorry ,
        rw primorial ,
        rw [<- @range_to_append 1 (2*m + 1) (2*(m+1))] ,
        {
        rw list.filter_append ,
        have r : range_to (2 * m + 1 + 1) (2 * (m + 1)) = [2 * (m+1)] := sorry,
        rw r ,
        have s : list.filter nat.prime [2 * (m + 1)] = [] := sorry ,
        rw s , simp ,
        have ih_bound : (1 + 2*m < (n+5)) := sorry ,
        have ih := primorial_bound (2*m + 1) sorry ,
        rw [<- primorial] ,
        rw nat.add_comm ,
        calc 8 * primorial (2 * m + 1) < 2 ^ (2 * (2 * m + 1)) : ih
        ... ≤ 2 ^ (2 * (2 * (m + 1))) : (le_2_pow_2_mul_2_mul_plus_1 m)
        },
        linarith , linarith ,
    },
    {
        cases h , rename h_w m , rw h_h at * ,
        have m_ge_2 : m ≥ 2 := sorry ,
        have h1 := primorial_2m_plus_1_le_power_2 m m_ge_2 ,
        have ih_bound : (m+1 < (n+5)) := sorry ,
        have h2 := primorial_bound (m+1) sorry ,
        calc 8 * primorial (2 * m + 1) ≤ 8 * primorial (m + 1) * 2 ^ (2*m) :        begin
                rw nat.mul_assoc ,
                apply nat.mul_le_mul_left , assumption ,
              end
        ... < 2 ^ (2 * (m+1)) * 2 ^ (2*m) :
            begin
                rw mul_lt_mul_right , assumption , exact sorry
            end
        ... = 2 ^ (2 * (2*m+1)) : sorry
    },
end

/- prime factorization -/

theorem factorize : ∀ (n m : ℕ) ,
    (∀ p , nat.prime p → p ∣ n → p ≤ m) →
    (∃ (r : ℕ → ℕ) , (∀ (p:ℕ) , nat.prime p → p ^ r p ∣ n) ∧ 
        n = (((range_to 1 m).filter nat.prime).map
            (λ p , p ^ (r p))).prod
    ) := sorry

lemma p_le_of_p_dvd_choose : ∀ (p n k : ℕ) ,
    k ≤ n → nat.prime p → p ∣ (choose n k) → p ≤ n :=
begin
    intros ,
    have q := @choose_mul_fact_mul_fact n k a,
    have r : (p ∣ nat.fact n) := begin
        cases a_2 , rw [a_2_h] at q , rw nat.mul_assoc at q ,
        rw nat.mul_assoc at q , rw <- q , apply dvd_mul_right ,
    end ,
    rw [nat.prime.dvd_fact] at r , assumption ,
    assumption ,
end

/- main result (bertrand's postulate for n ≥ 432 case) -/

lemma two_thirds_n_bound : ∀ (n : ℕ) ,
    n ≥ 468 → 
    2 * n / 3 < 2 →
    false := sorry

lemma p_le_2n_over_3 : ∀ (n p : ℕ) ,
    (∀ (x : ℕ), nat.prime x → n < x → 2 * n < x) →
    n ≥ 468 → 
    nat.prime p →
    p ∣ (choose (2*n) n) →
    p ≤ (2*n / 3) :=
begin
    intros ,
    by_cases (p ≤ 2*n / 3) ,
    {
        assumption ,
    },
    simp at h , rename h p_bound ,
    by_cases (p ≤ n) ,
    {
        have q := central_primes_do_not_divide p n a_2 (begin
            /- show p > 2 -/
            by_contradiction , simp at a_4 , rw a_4 at * ,
            apply two_thirds_n_bound , assumption, assumption,
        end) p_bound h ,
        contradiction ,
    },
    simp at h , clear p_bound , rename h p_bound ,
    {
        have q := a p a_2 p_bound ,
        have r := p_le_of_p_dvd_choose p (2*n) n a_2 a_3 ,
        linarith ,
    },
end

lemma factorize_choose_2n_n : ∀ (n : ℕ) ,
    (∀ (x : ℕ), nat.prime x → n < x → 2 * n < x) →
    n ≥ 468 → 
    ∃ (r : ℕ → ℕ) ,
    (∀ (p:ℕ) , nat.prime p → p ^ r p ∣ choose (2*n) n) ∧
    (choose (2*n) n =
        (((range_to 1 (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod) :=
begin
    intros ,
    have f := factorize (choose (2*n) n) (2*n/3) (begin
        intros , apply p_le_2n_over_3 , assumption, assumption, assumption,
        assumption ,
    end),
    cases f , rename f_w r , cases f_h , rename f_h_left dvd_condition ,
    rename f_h_right prod_condition ,
    existsi r ,
    split , assumption ,
    rw prod_condition ,
end

lemma prime_bounds_1 : ∀ (n : ℕ) (r : ℕ → ℕ),
    (∀ p , nat.prime p → p ^ r p ∣ (choose (2*n) n)) →
    (((range_to 1 (nat.sqrt (2*n))).filter nat.prime).map
                (λ p , p ^ (r p))).prod
    ≤ (2*n) ^ (nat.sqrt (2*n)) := sorry

lemma prime_bounds_2 : ∀ (n : ℕ) (r : ℕ → ℕ),
    (∀ p , nat.prime p → p ^ r p ∣ (choose (2*n) n)) →
    (((range_to (nat.sqrt (2*n) + 1) (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod
    ≤ primorial (2*n / 3) := sorry

lemma main_bound : ∀ (n : ℕ) ,
    n ≥ 468 →
    2*n * ((2*n) ^ (nat.sqrt (2*n))) * (4 ^ (2*n/3)) < 4^n := sorry

lemma b_lt_c_of_ab_lt_c : ∀ (a b c : ℕ) ,
    a > 0 → 
    a*b < c → b < c := sorry

lemma one_le_sqrt : ∀ (n : ℕ) ,
    468 ≤ n → 1 ≤ nat.sqrt (2 * n) := sorry

lemma sqrt_le_2_3 : ∀ (n : ℕ) ,
    468 ≤ n → nat.sqrt (2 * n) ≤ 2 * n / 3 := sorry

/- wtf why is this so hard? -/
lemma obvious_calculation_312 : 312 = 2 * 468 / 3 := sorry

/- TODO shouldn't need this (because bounded quantification) -/
local attribute [instance] prop_decidable

lemma bertrands_postulate_main : ∀ (n : ℕ) ,
    n ≥ 468 → 
    ∃ p , nat.prime p ∧ n < p ∧ p ≤ 2*n :=
begin
    intros , by_contradiction , simp at a_1 ,

    have h := factorize_choose_2n_n n a_1 a ,
    cases h , rename h_w r , cases h_h ,
    rename h_h_left r_divides ,
    rename h_h_right choose_2n_n_factorization ,

    have t := (
    calc 4^n ≤ 2*n * (choose (2*n) n) : four_n_bound n
    ... = 2*n * (((range_to 1 (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod : by rw choose_2n_n_factorization
    ... = 2*n *
            (((range_to 1 (nat.sqrt (2*n))).filter nat.prime).map
                (λ p , p ^ (r p))).prod *
            (((range_to (nat.sqrt (2*n) + 1) (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod :
            begin
                rw [@nat.mul_assoc (2*n) _ _] ,
                rw <- list.prod_append ,
                rw <- list.map_append ,
                rw <- list.filter_append ,
                rw <- range_to_append ,
                apply one_le_sqrt , assumption ,
                apply sqrt_le_2_3 , assumption ,
            end
    ... ≤ 2*n *
            (2*n) ^ (nat.sqrt (2*n)) *
            (((range_to (nat.sqrt (2*n) + 1) (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod :
            begin
                apply nat.mul_le_mul_right ,
                apply nat.mul_le_mul_left ,
                exact (prime_bounds_1 n r r_divides) ,
            end
    ... ≤ 2*n *
            (2*n) ^ (nat.sqrt (2*n)) *
            primorial (2*n / 3) :
            begin
                apply nat.mul_le_mul_left ,
                exact (prime_bounds_2 n r r_divides) ,
            end
    ... ≤ 2*n *
            (2*n) ^ (nat.sqrt (2*n)) *
            4 ^ (2*n/3) :
            begin
                have q := (calc
                        (3:ℕ) ≤ 312 : (by linarith)
                        ... = 2 * 468 / 3 : obvious_calculation_312
                        ... ≤ 2 * n / 3 : begin
                            apply nat.div_le_div_right ,
                            apply nat.mul_le_mul_left ,
                            assumption ,
                        end
                ),
                have h := primorial_bound (2*n / 3) q,
                have h' := b_lt_c_of_ab_lt_c _ _ _ (by linarith) h,
                rw nat.pow_mul at h' ,
                have h'' : (2 ^ 2 = 4) := by refl ,
                rw h'' at h' ,
                apply nat.mul_le_mul_left ,
                apply le_of_lt , assumption ,
            end
    ... < 4^n : main_bound n a
    ),
    linarith ,

end

/- full bertrand's postulate -/

theorem bertrands_postulate : ∀ (n : ℕ) ,
    n ≥ 1 →
    ∃ p , nat.prime p ∧ n < p ∧ p ≤ 2*n := sorry