import data.nat.modeq
import data.nat.basic
import data.int.basic
import data.nat.prime
import data.nat.gcd
import data.zmod.quadratic_reciprocity

#check zmodp.fermat_little

#check zmodp.eq_zero_iff_dvd_nat

lemma lcm_property (e d p q: ℕ) : (e*d = 1 % (nat.lcm p q)) → e*d -1 = 0 ∨ (∃ h: ℕ, e*d - 1 = h*(p - 1)) :=
begin
intro h,
sorry
end

/- These are the two major helper theorems for the RSA_correctness theorem -/
theorem RSA_lemma_modp (e d m p q: ℕ): ((nat.prime p ∧ nat.prime q ∧ p ≠ q) ∧ (e*d = 1 % (nat.lcm p q))) → (m^e)^d ≡ m [MOD p] :=
begin
    intro hyp,
    by_cases (m = 0 % p),
    {sorry},
    sorry
end

theorem RSA_lemma_modq (e d m p q: ℕ): ((nat.prime p ∧ nat.prime q ∧ p ≠ q) ∧ (e*d = 1 % (nat.lcm p q))) → (m^e)^d ≡ m [MOD q] :=
begin
    intro hyp,
    by_cases (m = 0 % p),
    {sorry},
    sorry
end

/- This is a small lemma that says that if you have two different primes, they are coprime. -/
#check nat.prime.coprime_iff_not_dvd
lemma coprime_prime_and_prime {p q : ℕ}: nat.prime p ∧ nat.prime q ∧ p ≠ q → nat.coprime p q :=
begin
intro hyp,
have h1: nat.prime p, from hyp.left,
have h2: nat.prime q, from (hyp.right).left,
have h3: p ≠ q, from (hyp.right).right,
have iff_conc: (nat.coprime p q ↔ ¬ p | q), from nat.prime.coprime_iff_not_dvd h1,
sorry
end

/- Technically you can get this theorem for all m in Z but to avoid casting we state it for nats -/
#check nat.modeq.modeq_and_modeq_iff_modeq_mul
theorem RSA_correctness (e d m p q: ℕ): ((nat.prime p ∧ nat.prime q ∧ p ≠ q) ∧ (e*d = 1 % (nat.lcm p q))) → (m^e)^d ≡ m [MOD (p*q)] :=
begin
    intro hyp,
    have hyp1: nat.prime p ∧ nat.prime q ∧ p ≠ q, from hyp.left,
    have h1: (m^e)^d ≡ m [MOD p], from RSA_lemma_modp e d m p q hyp,
    have h2: (m^e)^d ≡ m [MOD q], from RSA_lemma_modq e d m p q hyp,
     have h1andh2: (m^e)^d ≡ m [MOD p] ∧ (m^e)^d ≡ m [MOD q], from and.intro h1 h2,
    have h3: nat.coprime p q, from coprime_prime_and_prime hyp.left,
    have h4: ((m^e)^d ≡ m [MOD p] ∧ (m^e)^d ≡ m [MOD q]) ↔ (m^e)^d ≡ m [MOD p*q], from nat.modeq.modeq_and_modeq_iff_modeq_mul h3,
    have h5: (m^e)^d ≡ m [MOD p*q], from (iff.elim_left h4) h1andh2,
    exact h5
end
/-    intros e d m p q,
    or.elim (em (m = 0 % p))
    {sorry},
    sorry-/