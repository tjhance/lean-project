import data.nat.choose
import data.nat.prime
import data.nat.gcd
import tactic.linarith
import ring_theory.multiplicity

open classical
local attribute [instance] prop_decidable

lemma four_n_bound : ∀ (n : ℕ) ,
    4 ^ n ≤ 2 * n * (choose (2*n) n) := sorry

--def R (p:ℕ) (n:ℕ) : ℕ := multiplicity p (choose (2*n) n)

lemma p_to_R_bound : ∀ (p:ℕ) (r:ℕ) (n:ℕ) ,
    prime p →
    p ^ r ∣ (choose (2*n) n) →
    p ^ r ≤ 2*n := sorry

lemma central_primes_do_not_divide : ∀ (p n : ℕ) ,
    prime p →
    p ≠ 2 →
    2*n / 3 < p →
    p ≤ n →
    ¬ (p ∣ (choose (2*n) n)) := sorry

def primorial (n : ℕ) : ℕ :=
    (list.filter nat.prime (list.range' 1 n)).prod

def primorial_bound : ∀ (n : ℕ) ,
    n ≥ 3 →
    8 * primorial n < 2 ^ (2*n) := sorry

theorem factorize : ∀ (n m : ℕ) ,
    (∀ p , prime p → p ∣ n → p ≤ m) →
    (∃ (r : ℕ → ℕ) , (∀ (p:ℕ) , prime p → p ^ r p ∣ n) ∧ 
        n = (((list.range' 1 m).filter nat.prime).map
            (λ p , p ^ (r p))).prod
    ) := sorry

lemma p_le_2n_over_3 : ∀ (n p : ℕ) ,
    prime p →
    p ∣ (choose (2*n) n) →
    p ≤ (2*n / 3) := sorry

lemma factorize_choose_2n_n : ∀ (n : ℕ) ,
    ∃ (r : ℕ → ℕ) ,
    (∀ (p:ℕ) , prime p → p ^ r p ∣ choose (2*n) n) ∧
    (choose (2*n) n =
        (((list.range' 1 (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod) := sorry

theorem prime_bounds_1 : ∀ (n : ℕ) (r : ℕ → ℕ),
    (∀ p , prime p → p ^ r p ∣ (choose (2*n) n)) →
    (((list.range' 1 (nat.sqrt (2*n))).filter nat.prime).map
                (λ p , p ^ (r p))).prod
    ≤ (2*n) ^ (nat.sqrt (2*n)) := sorry

theorem prime_bounds_2 : ∀ (n : ℕ) (r : ℕ → ℕ),
    (∀ p , prime p → p ^ r p ∣ (choose (2*n) n)) →
    (((list.range' (nat.sqrt (2*n) + 1) (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod
    ≤ primorial (2*n / 3) := sorry

theorem main_bound : ∀ (n : ℕ) ,
    n ≥ 468 →
    2*n * ((2*n) ^ (nat.sqrt (2*n))) * (4 ^ (2*n/3)) < 4^n := sorry

lemma bertrands_postulate_main : ∀ (n : ℕ) ,
    n ≥ 468 → 
    ∃ p , prime p ∧ n < p ∧ p ≤ 2*n :=
begin
    intros , by_contradiction , simp at a_1 ,

    have h := factorize_choose_2n_n n ,
    cases h , rename h_w r , cases h_h ,
    rename h_h_left r_divides ,
    rename h_h_right choose_2n_n_factorization ,

    have t := (
    calc 4^n ≤ 2*n * (choose (2*n) n) : four_n_bound n
    ... = 2*n * (((list.range' 1 (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod : by rw choose_2n_n_factorization
    ... = 2*n *
            (((list.range' 1 (nat.sqrt (2*n))).filter nat.prime).map
                (λ p , p ^ (r p))).prod *
            (((list.range' (nat.sqrt (2*n) + 1) (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod : sorry
    ... ≤ 2*n *
            (2*n) ^ (nat.sqrt (2*n)) *
            primorial (2*n / 3) :
            begin
                have pb1 := prime_bounds_1 n r r_divides ,
                have pb2 := prime_bounds_2 n r r_divides ,
                exact sorry
            end
    ... ≤ 2*n *
            (2*n) ^ (nat.sqrt (2*n)) *
            4 ^ (2*n/3) :
            begin
                have h := primorial_bound (2*n / 3),
                exact sorry
            end
    ... < 4^n : main_bound n a
    ),
    linarith ,

end

theorem bertrands_postulate : ∀ (n : ℕ) ,
    n ≥ 1 →
    ∃ p , prime p ∧ n < p ∧ p ≤ 2*n := sorry