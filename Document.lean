/-
Independent Lean 4 verification of `document.tex`
  "윌슨 정리에 기반한 새로운 소수 판별 함수의 구성"
  (Construction of a new primality-detecting function based on Wilson's theorem)

NOTE ON IMPORTS.  `Mathlib.NumberTheory.Wilson` is deliberately NOT imported: it contains
`ZMod.wilsons_lemma` (a `simp` lemma!) and `Nat.prime_iff_fac_equiv_neg_one`, which would
directly discharge the document's central theorem.  The absence of those constants is
checked by `#eval` guards at the end of this file.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic
public import Mathlib.Util.AssertNoSorry

public section

namespace Document

open Finset
open scoped Nat

/-! ## §2  Preliminaries

The document's §2 fixes notation.  We record each notion as it is used below, and verify
the two statements §2 makes without proof (existence of modular inverses, and the
characterisation of the floor function). -/

/-- §2.1 Divisibility, `a ∣ b`. -/
theorem dvd_def' (a b : ℤ) : a ∣ b ↔ ∃ c : ℤ, b = a * c := Iff.rfl

/-- §2.2 Congruence: `a ≡ b (mod m)` means `m ∣ a - b`. -/
theorem congr_iff_dvd (a b : ℤ) (m : ℕ) : a ≡ b [ZMOD (m : ℤ)] ↔ (m : ℤ) ∣ a - b := by
  constructor
  · intro h; exact Int.modEq_iff_dvd.mp h.symm
  · intro h; exact (Int.modEq_iff_dvd.mpr h).symm

/-- §2.3 Existence of a modular inverse of `a` modulo `m` when `gcd(a, m) = 1`.
(The document asserts this without proof; here it is derived from Bézout's identity.) -/
theorem exists_modular_inverse {a : ℤ} {m : ℕ} (h : Int.gcd a (m : ℤ) = 1) :
    ∃ b : ℤ, a * b ≡ 1 [ZMOD (m : ℤ)] := by
  refine ⟨Int.gcdA a (m : ℤ), ?_⟩
  have hb := Int.gcd_eq_gcd_ab a (m : ℤ)
  rw [h] at hb
  rw [Int.modEq_iff_dvd]
  exact ⟨Int.gcdB a (m : ℤ), by push_cast at hb ⊢; linarith⟩

/-- §2.4 Characterisation of the floor: `⌊x⌋ = n ↔ x = n + α` for some `0 ≤ α < 1`. -/
theorem floor_spec (x : ℚ) (n : ℤ) :
    ⌊x⌋ = n ↔ ∃ α : ℚ, x = (n : ℚ) + α ∧ 0 ≤ α ∧ α < 1 := by
  rw [Int.floor_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x - n, by ring, by linarith, by linarith⟩
  · rintro ⟨α, rfl, h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- §2.5 The factorial as the product `∏_{k=1}^{n} k`, and the empty product `0! = 1`. -/
theorem factorial_eq_prod (n : ℕ) : n ! = ∏ k ∈ Finset.Icc 1 n, k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]

theorem factorial_zero' : (0)! = 1 := rfl

/-- §4 uses: `⌊a/b⌋` is the quotient of `a` divided by `b`, and `a = b·⌊a/b⌋ + r`
with `r` the remainder. -/
theorem floor_div_eq_quotient (a b : ℕ) : ⌊(a : ℚ) / (b : ℚ)⌋ = ((a / b : ℕ) : ℤ) := by
  exact_mod_cast Rat.floor_natCast_div_natCast a b

theorem div_add_rem (a b : ℕ) : a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm

/-! ## §3.1  Wilson's theorem, forward direction -/

section WilsonForward

variable {p : ℕ} [Fact p.Prime]

/-- Document, §3.1: if `a` is its own modular inverse then `p ∣ a² - 1 = (a+1)(a-1)`,
and since `p` is prime, `a ≡ ±1 (mod p)`. -/
theorem self_inv_eq_one_or_neg_one (a : ZMod p) (ha : a * a = 1) : a = 1 ∨ a = -1 := by
  have h : (a - 1) * (a + 1) = 0 := by linear_combination ha
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- Document, §3.1: every `k` with `1 < k < p-1` is paired with its modular inverse,
which is a *different* element of the same range; so the whole product `2·3·⋯·(p-2)`
collapses to `1`. -/
theorem prod_sdiff_three :
    ∏ x ∈ (univ : Finset (ZMod p)) \ {0, 1, -1}, x = 1 := by
  classical
  have hmem : ∀ a : ZMod p, a ∈ (univ : Finset (ZMod p)) \ {0, 1, -1} ↔
      a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by
    intro a; simp [Finset.mem_sdiff]
  refine Finset.prod_involution (fun a _ => a⁻¹) ?_ ?_ ?_ ?_
  · -- `a * a⁻¹ = 1`
    intro a ha
    exact mul_inv_cancel₀ ((hmem a).mp ha).1
  · -- the inverse of `a` is different from `a` unless `a = ±1`
    intro a ha _
    obtain ⟨h0, h1, hm1⟩ := (hmem a).mp ha
    intro hcon
    have h' : a * a⁻¹ = 1 := mul_inv_cancel₀ h0
    rw [hcon] at h'
    rcases self_inv_eq_one_or_neg_one a h' with h | h
    · exact h1 h
    · exact hm1 h
  · -- the inverse stays inside the range
    intro a ha
    obtain ⟨h0, h1, hm1⟩ := (hmem a).mp ha
    refine (hmem _).mpr ⟨inv_ne_zero h0, ?_, ?_⟩
    · intro h; exact h1 (by simpa using congrArg (· ⁻¹) h)
    · intro h; exact hm1 (by simpa using congrArg (· ⁻¹) h)
  · intro a _; exact inv_inv a

/-- The product of all nonzero residues is `-1`:  `1 · (p-1) · (2·3·⋯·(p-2)) = -1`. -/
theorem prod_nonzero (hp2 : p ≠ 2) :
    ∏ x ∈ (univ : Finset (ZMod p)) \ {0}, x = -1 := by
  classical
  have hp : p.Prime := Fact.out
  have hlt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have : Fact (2 < p) := ⟨hlt⟩
  have hne : (1 : ZMod p) ≠ -1 := fun h => (ZMod.neg_one_ne_one (n := p)) h.symm
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hm10 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr h10
  have hsub : ({1, -1} : Finset (ZMod p)) ⊆ (univ : Finset (ZMod p)) \ {0} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    rcases hx with rfl | rfl
    · exact h10
    · exact hm10
  have hset : ((univ : Finset (ZMod p)) \ {0}) \ ({1, -1} : Finset (ZMod p))
      = (univ : Finset (ZMod p)) \ {0, 1, -1} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
  have := Finset.prod_sdiff (f := fun x : ZMod p => x) hsub
  rw [hset, prod_sdiff_three, one_mul, Finset.prod_pair hne, one_mul] at this
  exact this.symm

/-- `(p-1)!`, read in `ZMod p`, is the product of all nonzero residues. -/
theorem factorial_eq_prod_nonzero :
    (((p - 1)! : ℕ) : ZMod p) = ∏ x ∈ (univ : Finset (ZMod p)) \ {0}, x := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩  -- `p ≠ 0`
  have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.pos
  have h1 : ((p - 1)! : ℕ) = ∏ x ∈ Ico 1 p, x := by
    rw [← Finset.prod_Ico_id_eq_factorial (p - 1), hp1]
  rw [h1, Nat.cast_prod]
  refine Finset.prod_nbij' (fun n : ℕ => (n : ZMod p)) (fun x : ZMod p => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Ico] at ha
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    intro hcon
    have : ((a : ZMod p)).val = a := ZMod.val_cast_of_lt ha.2
    rw [hcon, ZMod.val_zero] at this
    omega
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hx
    rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt x⟩
    rcases Nat.eq_zero_or_pos x.val with h | h
    · exact absurd ((ZMod.val_eq_zero x).mp h) hx
    · exact h
  · intro a ha
    rw [Finset.mem_Ico] at ha
    exact ZMod.val_cast_of_lt ha.2
  · intro x _
    simp
  · intro a _; rfl

/-- **Wilson's theorem, (→)**  (document §3.1). -/
theorem wilson_forward (hp : p.Prime) : (((p - 1)! : ℕ) : ZMod p) = -1 := by
  rcases eq_or_ne p 2 with rfl | hp2
  · decide +revert
  · rw [factorial_eq_prod_nonzero, prod_nonzero hp2]

end WilsonForward


/-! ## §3.1  Wilson's theorem, converse direction

The document's argument: if `n` is composite, pick a divisor `a` of `n` with `1 < a < n`.
Then `a ∣ n ∣ (n-1)! + 1` and `a ∣ (n-1)!` (because `a ≤ n-1`), hence `a ∣ 1`, contradiction. -/

/-- **Wilson's theorem, (←)**  (document §3.1). -/
theorem wilson_converse {n : ℕ} (hn : 1 < n) (h : (((n - 1)! : ℕ) : ZMod n) = -1) :
    n.Prime := by
  by_contra hcomp
  obtain ⟨a, hadvd, ha2, han⟩ := Nat.exists_dvd_of_not_prime2 hn hcomp
  -- `n ∣ (n-1)! + 1`
  have hn_dvd : n ∣ ((n - 1)! + 1 : ℕ) := by
    have : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := by push_cast [h]; ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp this
  -- `a ∣ n ∣ (n-1)! + 1`
  have h1 : a ∣ ((n - 1)! + 1 : ℕ) := hadvd.trans hn_dvd
  -- `a ≤ n - 1`, hence `a ∣ (n-1)!`
  have h2 : a ∣ ((n - 1)! : ℕ) := Nat.dvd_factorial (by omega) (by omega)
  -- so `a ∣ 1`
  have h3 : a ∣ 1 := (Nat.dvd_add_right h2).mp h1
  exact absurd (Nat.dvd_one.mp h3) (by omega)

/-- **Wilson's theorem** as stated in the document, §3.1: for `n > 1`,
`n` is prime iff `(n-1)! ≡ -1 (mod n)`. -/
theorem wilson {n : ℕ} (hn : 1 < n) :
    n.Prime ↔ (((n - 1)! : ℕ) : ZMod n) = -1 := by
  constructor
  · intro hp
    have : Fact n.Prime := ⟨hp⟩
    exact wilson_forward hp
  · exact wilson_converse hn

/-- The same statement in the integer-congruence notation of the document:
`(n-1)! ≡ -1 (mod n)`. -/
theorem wilson_intModEq {n : ℕ} (hn : 1 < n) :
    n.Prime ↔ (((n - 1)! : ℕ) : ℤ) ≡ -1 [ZMOD (n : ℤ)] := by
  rw [wilson hn, Int.ModEq]
  constructor
  · intro h
    have : ((((n - 1)! : ℕ) : ℤ) : ZMod n) = ((-1 : ℤ) : ZMod n) := by push_cast [h]; ring
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this
  · intro h
    have : ((((n - 1)! : ℕ) : ℤ) : ZMod n) = ((-1 : ℤ) : ZMod n) :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
    push_cast at this
    exact this

/-! ## §3.2  Lemma: every composite `n > 4` divides `(n-1)!` -/

/-- Two *distinct* factors taken from `1, 2, …, n-1` multiply to a divisor of `(n-1)!`. -/
theorem mul_dvd_factorial_pred {a b n : ℕ} (hab : a ≠ b) (ha1 : 1 ≤ a) (han : a < n)
    (hb1 : 1 ≤ b) (hbn : b < n) : a * b ∣ (n - 1)! := by
  classical
  have hfac : ((n - 1)! : ℕ) = ∏ i ∈ Ico 1 n, i := by
    have hn1 : n - 1 + 1 = n := by omega
    rw [← Finset.prod_Ico_id_eq_factorial (n - 1), hn1]
  have hsub : ({a, b} : Finset ℕ) ⊆ Ico 1 n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [Finset.mem_Ico] <;> omega
  have h := Finset.prod_dvd_prod_of_subset ({a, b} : Finset ℕ) (Ico 1 n) (fun i => i) hsub
  rw [Finset.prod_pair hab] at h
  rw [hfac]
  exact h

/-- **Lemma 3.2** of the document: `n ∣ (n-1)!` for every composite `n > 4`.

The document splits into the case where `n = ab` with `1 < a < b < n` and the remaining
case, in which it argues `n = p²` for a prime `p`, using `p` and `2p` as the two factors. -/
theorem lemma_composite_dvd_factorial {n : ℕ} (hn : 4 < n) (hcomp : ¬ n.Prime) :
    n ∣ (n - 1)! := by
  by_cases hcase : ∃ a b : ℕ, n = a * b ∧ 1 < a ∧ a < b ∧ b < n
  · -- Case 1 of the document: a genuine factorisation into two *different* factors.
    obtain ⟨a, b, hnab, ha1, hab, hbn⟩ := hcase
    have : a < n := by omega
    rw [hnab]
    exact mul_dvd_factorial_pred (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- Case 2 of the document: no such factorisation, hence `n = p^2` with `p` prime.
    push Not at hcase
    obtain ⟨p, hp, hpdvd, hple⟩ :
        ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, 1 < q → q ∣ n → p ≤ q :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n,
        fun q hq hqd => Nat.minFac_le_of_dvd hq hqd⟩
    obtain ⟨m, hm⟩ := hpdvd
    have hp1 : 1 < p := hp.one_lt
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · interval_cases m
        · omega                      -- `m = 0` would give `n = 0`
        · exact absurd (by rw [hm, mul_one]; exact hp) hcomp   -- `m = 1` gives `n = p` prime
      · omega
    have hmn : m < n := by nlinarith
    have hpm : p ≤ m := hple m hm1 ⟨p, by rw [hm]; ring⟩
    -- the excluded factorisation forces `p = m`
    have hpeqm : p = m := by
      rcases lt_or_eq_of_le hpm with h | h
      · exact absurd (hcase p m hm hp1 h) (by omega)
      · exact h
    -- hence `n = p^2`, and `p ≥ 3` because `n > 4`
    have hnp2 : n = p * p := by rw [hm, hpeqm]
    have hp3 : 3 ≤ p := by
      rcases eq_or_lt_of_le hp.two_le with h | h
      · exfalso; rw [← h] at hnp2; omega
      · omega
    -- `p` and `2p` are two different elements of `{1, …, n-1}`
    have h2p : 2 * p < n := by nlinarith
    have hdvd : p * (2 * p) ∣ (n - 1)! :=
      mul_dvd_factorial_pred (by omega) (by omega) (by omega) (by omega) h2p
    exact dvd_trans ⟨2, by rw [hnp2]; ring⟩ hdvd

/-! ## §4  Construction of the primality-detecting function -/

/-- The first display of §4: for `n > 1` with `n ≠ 4`, the remainder of `(n-1)!` modulo `n`
is `n-1` when `n` is prime and `0` when `n` is composite.  This combines Wilson's theorem
with Lemma 3.2 and the observation that every composite `≠ 4` is `> 4`. -/
theorem factorial_mod (n : ℕ) (hn : 1 < n) (h4 : n ≠ 4) :
    ((n - 1)! : ℕ) % n = if n.Prime then n - 1 else 0 := by
  by_cases hp : n.Prime
  · simp only [hp, ↓reduceIte]
    have hcast : (((n - 1 : ℕ)) : ZMod n) = -1 := by
      rw [Nat.cast_sub (show 1 ≤ n by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
    have hw : (((n - 1)! : ℕ) : ZMod n) = (((n - 1 : ℕ)) : ZMod n) := by
      rw [hcast, (wilson hn).mp hp]
    have hmod : ((n - 1)! : ℕ) ≡ (n - 1) [MOD n] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hw
    rw [Nat.ModEq] at hmod
    rw [hmod, Nat.mod_eq_of_lt (by omega)]
  · simp only [hp, ↓reduceIte]
    -- a composite `≠ 4` is `> 4`
    have h5 : 4 < n := by
      rcases Nat.lt_or_ge n 5 with h | h
      · interval_cases n <;> simp_all (config := { decide := true })
      · omega
    exact Nat.dvd_iff_mod_eq_zero.mp (lemma_composite_dvd_factorial h5 hp)

/-- The document's "new primality-detecting function"
`1_P(n) = (n-2)! - n/(n-1)·⌊(n-1)!/n⌋ - (2/3)·⌊1/((n-4)²+1)⌋`. -/
noncomputable def primeDetector (n : ℕ) : ℚ :=
  (((n - 2)! : ℕ) : ℚ)
    - (n : ℚ) / ((n : ℚ) - 1) * (⌊((((n - 1)! : ℕ)) : ℚ) / (n : ℚ)⌋ : ℤ)
    - (2 / 3) * (⌊(1 : ℚ) / (((n : ℚ) - 4) ^ 2 + 1)⌋ : ℤ)

/-- The correction term `⌊1/((n-4)²+1)⌋` is `1` at `n = 4` and `0` everywhere else. -/
theorem correction_term (n : ℕ) :
    ⌊(1 : ℚ) / (((n : ℚ) - 4) ^ 2 + 1)⌋ = if n = 4 then 1 else 0 := by
  by_cases h : n = 4
  · subst h; norm_num
  · simp only [h, ↓reduceIte]
    have hsq : (1 : ℚ) ≤ ((n : ℚ) - 4) ^ 2 := by
      rcases Nat.lt_or_ge n 4 with hlt | hge
      · have : (n : ℚ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.mp hlt
        nlinarith
      · have : (5 : ℚ) ≤ (n : ℚ) := by
          have : 5 ≤ n := by omega
          exact_mod_cast this
        nlinarith
    have hpos : (0 : ℚ) < ((n : ℚ) - 4) ^ 2 + 1 := by nlinarith
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hpos]
    nlinarith

/-- Algebraic core of §4.  Dividing the remainder `(n-1)! - n⌊(n-1)!/n⌋` by `n-1`
really does produce the document's first two terms:
`(n-2)! - n/(n-1)·⌊(n-1)!/n⌋ = ((n-1)! mod n)/(n-1)`. -/
theorem two_terms_eq (n : ℕ) (hn : 1 < n) :
    (((n - 2)! : ℕ) : ℚ)
        - (n : ℚ) / ((n : ℚ) - 1) * (⌊((((n - 1)! : ℕ)) : ℚ) / (n : ℚ)⌋ : ℤ)
      = (((((n - 1)! % n : ℕ))) : ℚ) / ((n : ℚ) - 1) := by
  have hnQ : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn1 : ((n : ℚ) - 1) ≠ 0 := by linarith
  have hfloor : ⌊((((n - 1)! : ℕ)) : ℚ) / (n : ℚ)⌋ = ((((n - 1)! / n : ℕ)) : ℤ) := by
    exact_mod_cast Rat.floor_natCast_div_natCast ((n - 1)!) n
  rw [hfloor, Int.cast_natCast]
  have hfac : ((n - 1)! : ℕ) = (n - 1) * ((n - 2)! : ℕ) := by
    have h : n - 1 = (n - 2) + 1 := by omega
    rw [h, Nat.factorial_succ]
  have h1 : ((((n - 1)! : ℕ)) : ℚ) = ((n : ℚ) - 1) * ((((n - 2)! : ℕ)) : ℚ) := by
    rw [hfac]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
    ring
  have h2 : ((((n - 1)! : ℕ)) : ℚ)
      = (n : ℚ) * ((((n - 1)! / n : ℕ)) : ℚ) + ((((n - 1)! % n : ℕ)) : ℚ) := by
    conv_lhs => rw [← Nat.div_add_mod ((n - 1)!) n]
    push_cast
    ring
  field_simp
  linarith [h1, h2]

/-- **The main theorem of the document (§4).**  For every natural number `n > 1`,
the constructed function returns `1` on primes and `0` on composites. -/
theorem primeDetector_eq_indicator (n : ℕ) (hn : 1 < n) :
    primeDetector n = if n.Prime then 1 else 0 := by
  have hnQ : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn1 : ((n : ℚ) - 1) ≠ 0 := by linarith
  rw [primeDetector, two_terms_eq n hn, correction_term n]
  by_cases h4 : n = 4
  · subst h4
    norm_num [Nat.factorial]
  · simp only [h4, ↓reduceIte]
    rw [factorial_mod n hn h4]
    by_cases hp : n.Prime
    · simp only [hp, ↓reduceIte]
      push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
      field_simp
      ring
    · simp only [hp, ↓reduceIte]
      norm_num

/-! ## §4  The intermediate ("uncorrected") function and why the correction is needed -/

/-- The function the document obtains *before* the `n = 4` correction:
`(n-2)! - n/(n-1)·⌊(n-1)!/n⌋`. -/
noncomputable def primeDetectorUncorrected (n : ℕ) : ℚ :=
  (((n - 2)! : ℕ) : ℚ)
    - (n : ℚ) / ((n : ℚ) - 1) * (⌊((((n - 1)! : ℕ)) : ℚ) / (n : ℚ)⌋ : ℤ)

/-- The document claims this intermediate function detects primality "for `n > 4`".
In fact it already works for **every** `n > 1` other than `n = 4`. -/
theorem primeDetectorUncorrected_eq (n : ℕ) (hn : 1 < n) (h4 : n ≠ 4) :
    primeDetectorUncorrected n = if n.Prime then 1 else 0 := by
  have hnQ : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn1 : ((n : ℚ) - 1) ≠ 0 := by linarith
  rw [primeDetectorUncorrected, two_terms_eq n hn, factorial_mod n hn h4]
  by_cases hp : n.Prime
  · simp only [hp, ↓reduceIte]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
    field_simp
  · simp only [hp, ↓reduceIte]
    norm_num

/-- The document's computation at the exceptional point: the uncorrected function
takes the value `2/3` at `n = 4` instead of `0`.  (This is what the third term repairs.) -/
theorem primeDetectorUncorrected_four : primeDetectorUncorrected 4 = 2 / 3 := by
  norm_num [primeDetectorUncorrected, Nat.factorial]

/-- Consequently the uncorrected function is *not* a primality indicator at `n = 4`. -/
theorem primeDetectorUncorrected_four_ne : primeDetectorUncorrected 4 ≠ 0 := by
  rw [primeDetectorUncorrected_four]; norm_num

/-! ## Independent numerical spot checks of the final formula -/

example : primeDetector 2 = 1 := by norm_num [primeDetector, Nat.factorial]
example : primeDetector 3 = 1 := by norm_num [primeDetector, Nat.factorial]
example : primeDetector 4 = 0 := by norm_num [primeDetector, Nat.factorial]
example : primeDetector 5 = 1 := by norm_num [primeDetector, Nat.factorial]
example : primeDetector 6 = 0 := by norm_num [primeDetector, Nat.factorial]
example : primeDetector 7 = 1 := by norm_num [primeDetector, Nat.factorial]
example : primeDetector 8 = 0 := by norm_num [primeDetector, Nat.factorial]
example : primeDetector 9 = 0 := by norm_num [primeDetector, Nat.factorial]
example : primeDetector 10 = 0 := by norm_num [primeDetector, Nat.factorial]
example : primeDetector 11 = 1 := by norm_num [primeDetector, Nat.factorial]

/-! ## Sharpness of the hypotheses

These checks confirm that each restriction appearing in the document is really needed. -/

/-- The hypothesis `n > 1` in Wilson's theorem is necessary: for `n = 1` the congruence
`(n-1)! ≡ -1 (mod n)` holds (everything is congruent modulo `1`) while `1` is not prime,
so the converse direction would be false without it.  The document states the restriction. -/
theorem wilson_needs_one_lt : (((1 - 1)! : ℕ) : ZMod 1) = -1 ∧ ¬ Nat.Prime 1 :=
  ⟨Subsingleton.elim _ _, by norm_num⟩

/-- Lemma 3.2 genuinely fails at `n = 4`: `4 ∤ 3! = 6`.  This is why `n = 4` has to be
excluded there and corrected separately in §4. -/
theorem lemma_fails_at_four : ¬ ((4 : ℕ) ∣ (4 - 1)!) := by decide

/-- `4` is the only composite that is not `> 4`, which is the (correct) step the document
uses to apply Lemma 3.2 to every composite `n ≠ 4`. -/
theorem composite_ne_four_gt_four {n : ℕ} (hn : 1 < n) (hcomp : ¬ n.Prime) (h4 : n ≠ 4) :
    4 < n := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp_all (config := { decide := true })
  · omega

/-- Remark on the domain of the final formula.  The document restricts to `n > 1`, and must:
the factor `n/(n-1)` is undefined at `n = 1`.  (With Lean's convention `x / 0 = 0` the
literal expression evaluates to `1` there, i.e. it would report "1 is prime".) -/
example : primeDetector 1 = 1 := by norm_num [primeDetector, Nat.factorial]

/-! ## Verification guards

(1) None of the Mathlib results that would directly settle the document's central claims
are even present in the environment of this file.  (`FiniteField.prod_univ_units_id_eq_neg_one`,
the finite-field product formula from which Mathlib derives Wilson's lemma, *is* reachable
through the imports, but it carries no `simp` attribute and is never mentioned in this file:
the pairing argument of §3.1 is carried out explicitly in `prod_sdiff_three`.) -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in [`ZMod.wilsons_lemma, `Nat.prime_iff_fac_equiv_neg_one,
            `Nat.prime_of_fac_equiv_neg_one, `ZMod.prod_Ico_one_prime] do
    if env.contains n then
      throwError "the forbidden Mathlib lemma {n} is in scope in this file"
  logInfo "guard: no Wilson-type Mathlib shortcut is in scope"

/-! (2) No `sorry` anywhere, and the only axioms used are Lean's three standard ones. -/

assert_no_sorry wilson
assert_no_sorry wilson_intModEq
assert_no_sorry lemma_composite_dvd_factorial
assert_no_sorry factorial_mod
assert_no_sorry primeDetector_eq_indicator
assert_no_sorry primeDetectorUncorrected_eq

#print axioms wilson
#print axioms lemma_composite_dvd_factorial
#print axioms primeDetector_eq_indicator
#print axioms primeDetectorUncorrected_eq

end Document
