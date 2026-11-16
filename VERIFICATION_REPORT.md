# Lean 4 verification of `document.tex`

Formal verification of **"윌슨 정리에 기반한 새로운 소수 판별 함수의 구성"** (이우진) —
the construction of a primality-detecting function from Wilson's theorem.

| | |
| --- | --- |
| Source document | `document.tex` (unmodified) |
| Formalisation | [`Document.lean`](Document.lean), 496 lines |
| Toolchain | Lean 4.36.0-rc2, Mathlib `v4.36.0-rc2` |
| Build | `lake build` — 6317 jobs, 0 errors, 0 warnings |
| `sorry` / `admit` / extra axioms | none |
| Date | 2026-11-16 |

**Verdict: every mathematical claim in the document is correct.** The final formula

```latex
\mathbf{1}_\mathbb{P}(n) = (n-2)! - \frac{n}{n-1}\left\lfloor \frac{(n-1)!}{n} \right\rfloor - \frac{2}{3}\left\lfloor \frac{1}{(n-4)^2+1} \right\rfloor
```

is a correct primality indicator for **every** natural `n > 1` — not merely for `n > 4`, as the
document claims. Seven gaps were found in the write-up; none of them changes a result, and no
statement requires mathematical correction.

## 1. Statements extracted from the document

| § | Statement |
| --- | --- |
| 1 | Definition of `1_P(n)` for `n > 1`: 1 on primes, 0 on composites |
| 2.1 | Divisibility `a ∣ b` |
| 2.2 | Congruence `a ≡ b (mod m)` ⟺ `m ∣ a − b`; informal remark that congruences support most properties of equations except division |
| 2.3 | Existence of a modular inverse of `a` mod `m` when `gcd(a, m) = 1` (asserted, not proved) |
| 2.4 | Floor: `⌊x⌋ = n` ⟺ `x = n + α` with `0 ≤ α < 1` |
| 2.5 | Factorial as `∏_{k=1}^{n} k`, with `0! = 1` as the empty product |
| 3.1 | **Wilson's theorem:** for `n > 1`, `n` prime ⟺ `(n−1)! ≡ −1 (mod n)`, with proofs of both directions |
| 3.2 | **Lemma:** every composite `n > 4` satisfies `n ∣ (n−1)!`, proved in two cases |
| 4 | `(n−1)! mod n` equals `n−1` (prime) or `0` (composite) for `n ≠ 4` |
| 4 | Remainder `= (n−1)! − n⌊(n−1)!/n⌋`; dividing by `n−1` gives `(n−2)! − n/(n−1)·⌊(n−1)!/n⌋` |
| 4 | That intermediate function evaluates to `2/3` at `n = 4` |
| 4 | `⌊1/((n−4)²+1)⌋` is 1 at `n = 4` and 0 otherwise |
| 4 | **Final formula** (above) |

## 2. What was verified in Lean

| § | Statement | Lean declaration | Status |
| --- | --- | --- | --- |
| 2.2 | congruence ⟺ divisibility | `congr_iff_dvd` | proved |
| 2.3 | existence of modular inverses | `exists_modular_inverse` | proved (via Bézout) |
| 2.4 | floor characterisation | `floor_spec` | proved |
| 2.5 | factorial as a product, `0! = 1` | `factorial_eq_prod`, `factorial_zero'` | proved |
| 3.1 | `a² ≡ 1 (mod p)` ⟹ `a ≡ ±1` | `self_inv_eq_one_or_neg_one` | proved |
| 3.1 | `2·3⋯(p−2) ≡ 1` by inverse pairing | `prod_sdiff_three` | proved |
| 3.1 | product of all non-zero residues `= −1` | `prod_nonzero` | proved |
| 3.1 | `(p−1)!` as that product | `factorial_eq_prod_nonzero` | proved |
| 3.1 | **Wilson (→)** | `wilson_forward` | proved |
| 3.1 | **Wilson (←)** | `wilson_converse` | proved |
| 3.1 | **Wilson (⟺)** | `wilson`, `wilson_intModEq` | proved |
| 3.2 | two distinct factors `< n` divide `(n−1)!` | `mul_dvd_factorial_pred` | proved |
| 3.2 | **Lemma:** composite `n > 4` ⟹ `n ∣ (n−1)!` | `lemma_composite_dvd_factorial` | proved |
| 4 | `(n−1)! mod n` for `n ≠ 4` | `factorial_mod` | proved |
| 4 | remainder divided by `n−1` | `two_terms_eq` | proved |
| 4 | correction term | `correction_term` | proved |
| 4 | **Main theorem** | `primeDetector_eq_indicator` | proved |
| 4 | intermediate function is an indicator for `n > 1`, `n ≠ 4` | `primeDetectorUncorrected_eq` | proved |
| 4 | intermediate function `= 2/3` at `n = 4` | `primeDetectorUncorrected_four` | confirmed |

Plus numeric spot checks of the formula at `n = 2 … 11`, and three sharpness lemmas
(`wilson_needs_one_lt`, `lemma_fails_at_four`, `composite_ne_four_gt_four`) showing that the
hypotheses `n > 1`, `n ≠ 4` and "composite" cannot be dropped.

**Wilson's theorem is proved from first principles.** `Mathlib.NumberTheory.Wilson` is deliberately
not imported, and a compile-time guard in `Document.lean` fails the build if `ZMod.wilsons_lemma`
(a `simp` lemma that would close the goal in one step), `Nat.prime_iff_fac_equiv_neg_one`,
`Nat.prime_of_fac_equiv_neg_one` or `ZMod.prod_Ico_one_prime` ever come into scope.

## 3. Gaps found in the original proofs

None is fatal; each is a step the reader must supply.

1. **The pairing is justified backwards (§3.1).** The text says `2·3⋯(p−2)` collapses *because* the
   count `p−3` is even. Evenness does not imply pairing. The actual content is that `k ↦ k*` is a
   fixed-point-free involution; evenness is a consequence of it.
2. **Missing closure check (§3.1).** The pairing also requires `k* ∈ {2, …, p−2}`, i.e.
   `k* ≠ 0, 1, p−1`. The document never verifies this. In Lean it is an unavoidable obligation
   (`g_mem` in `prod_sdiff_three`).
3. **"정수 n" in the converse (§3.1).** The converse paragraph begins with an *integer* `n` but
   silently needs `1 < n` (for `a ≤ n−1`, and to exclude `n = 1`). The hypothesis is present in the
   theorem statement, so this is wording only — but it is not vacuous: `n = 1` satisfies
   `(n−1)! ≡ −1 (mod n)` and is not prime (`wilson_needs_one_lt`).
4. **Unproved sub-claim (§3.2, case 2).** "Exactly one non-trivial divisor exists, hence `n = p²`
   with `p` prime" is asserted. It needs (i) that divisors pair off as `d ↔ n/d`, and (ii) that the
   single divisor is itself prime.
5. **Compressed step (§3.2, case 2).** "`n > 4`, hence `n > 2p`" uses `p ≥ 3` (from `p² > 4`), and
   the conclusion needs `2p ≤ n−1`.
6. **Domain mismatch (§4).** The text says "consider only `n ≠ 4`", derives the formula, then claims
   it works "for `n > 4`". The correct and verified claim is: for **all** `n > 1` with `n ≠ 4`, so
   `n = 2` and `n = 3` work too. With the correction term, the final formula holds for all `n > 1`.
7. **Implicit domain conditions (§4).** `(n−1)!/(n−1) = (n−2)!` needs `n ≥ 2`, and `n/(n−1)` needs
   `n ≠ 1`; both are covered by the §1 restriction `n > 1`, which is genuinely necessary — the
   formula is undefined at `n = 1`.

One further remark: the division by `n−1` is applied to the integer *value* of the remainder, not
inside a congruence, so §2.2's warning that congruences do not support division is not violated.

## 4. Statements requiring mathematical correction

**None.** No theorem, lemma or formula in the document is false, and no stated result is missing a
hypothesis. The only change worth making is the wording in §4: replace "a primality function for
`n > 4`" with "for every `n > 1` other than `n = 4`".

## 5. Differences between the original proofs and the Lean proofs

- **Wilson (→).** The document pairs the residues `2, …, p−2`; Lean pairs the elements of
  `(ZMod p) \ {0, 1, −1}` using `Finset.prod_involution` — the same involution, stated residue-wise.
  The bridge `((p−1)! : ZMod p) = ∏ non-zero residues`, which the document takes for granted, is
  proved by an explicit bijection `k ↦ (k : ZMod p)` on `Ico 1 p`. The case `p = 2` is separate, as
  in the document.
- **Lemma 3.2, case 2.** Instead of divisor counting, Lean takes `p = minFac n`, writes `n = p·m`,
  and shows the excluded factorisation forces `p = m`, hence `n = p²` — a complete version of the
  step the document asserts. The rest (`p` and `2p` as distinct factors `< n`) is identical.
- **§4.** The informal remainder reasoning is replaced by `(n−1)! = n·q + r` over ℕ with
  `q = (n−1)!/n`, `r = (n−1)! % n`, plus `⌊(a:ℚ)/(b:ℚ)⌋ = a/b`; the identity
  `(n−2)! − n/(n−1)·q = r/(n−1)` is then field algebra (`two_terms_eq`).
- **Not formalised.** §2.2's informal remark about congruences has no formal content.

## 6. Build result

```
$ lake build
Build completed successfully (6317 jobs).

guard: no Wilson-type Mathlib shortcut is in scope
'Document.wilson' depends on axioms: [propext, Classical.choice, Quot.sound]
'Document.lemma_composite_dvd_factorial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Document.primeDetector_eq_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Document.primeDetectorUncorrected_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`assert_no_sorry` passes for all six main theorems. No unresolved verification issues.

**One caveat.** Mathlib's finite-field product formula
`FiniteField.prod_univ_units_id_eq_neg_one` — from which Mathlib derives Wilson's lemma — is
reachable through the imports. It carries no `simp` attribute and never appears in `Document.lean`
(the pairing argument is written out in full), but Lean 4.36's module system hides imported proof
terms, so an automated transitive-dependency check was not possible. That single point rests on
inspection rather than on a machine check.

## Reproducing

```
lake exe cache get   # optional: prebuilt Mathlib oleans
lake build
```

`document.tex` was not modified. The only configuration change is a `[[lean_lib]] Document` entry in
`lakefile.toml` (plus its default-target name) so that plain `lake build` checks the formalisation.
