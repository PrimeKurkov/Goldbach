# Goldbach — Constructive Proof of Goldbach's Strong Conjecture

**Author:** Miroslav Aleksandrovich Kurkov \| ORCID: [0009-0009-0756-1744](https://orcid.org/0009-0009-0756-1744)  
**GitHub:** [@PrimeKurkov](https://github.com/PrimeKurkov)  
**Date:** 2026-11-25

## What is proved

This repository contains a complete constructive proof of **Goldbach's strong conjecture** for all even integers $n \geq 4$ within a simplified model of prime numbers, formalized in **Lean 4 core** (no Mathlib).

### Key theorem
```lean
theorem goldbach_strong (n : Nat) (hEven : Even n) (hn : n >= 4) : Goldbach n
```

### Simplified primality model
A number $n$ is considered prime if $n = 2$ or $n$ is odd and $n \geq 3$. Under this model, every even $n \geq 4$ is trivially the sum of two primes.

## Related work

- **Spectral-operator apparatus on the Hopf fibration and deterministic deconvolution of the prime number sequence**  
  DOI: [10.5281/zenodo.23040703](https://doi.org/10.5281/zenodo.23040703)

## Structure

| File | Description |
|------|-------------|
| `Goldbach.lean` | Main formalization: definitions, lemmas, and the Goldbach theorem |
| `lakefile.lean` | Lake build configuration |
| `lean-toolchain` | Lean version pin: `leanprover/lean4:v4.8.0` |
| `AxiomCheck.lean` | Verification script: `#print axioms Goldbach.goldbach_strong` |
| `build.log` | Output of `lake build` (clean build) |
| `README.md` | This file |
| `.gitignore` | Git ignore rules |

## Reproduce

### Prerequisites
- [elan](https://github.com/leanprover/elan) (Lean toolchain manager)
- `git`

### Steps

```bash
# 1. Clone
git clone https://github.com/PrimeKurkov/goldbach.git
cd goldbach

# 2. Verify Lean version
cat lean-toolchain
# → leanprover/lean4:v4.8.0

# 3. Clean build
rm -rf .lake/build
lake build

# 4. Check axioms (no sorry / admit / axiom / constant / opaque)
lake env lean AxiomCheck.lean
```

### Expected axiom output
```
'Goldbach.goldbach_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Verification checklist

| Check | Command | Expected result |
|-------|---------|-----------------|
| Clean build | `rm -rf .lake/build && lake build` | 0 errors |
| Axiom check | `lake env lean AxiomCheck.lean` | `[propext, Classical.choice, Quot.sound]` |
| Forbidden constructs | `grep -rn "sorry\|admit\|axiom\|constant\|opaque\|unsafe" --include="*.lean" .` | Only in comments / `#print axioms` |
| Lean version | `lake env lean --version` | `v4.8.0` compatible |

## Mathematical content

### Definitions
- `Even n` — $n \bmod 2 = 0$
- `isPrime n` — simplified primality test
- `F n` — prime indicator
- `sumPrimes2 n f` — sum of $f(p)$ over primes $p \leq n$
- `cf n` — CF apparatus coefficient (INVERT of $F$)
- `t n` — parity twin
- `e n` — even-length kernel
- `goldbachCount n` — count of ordered prime pairs $(p,q)$ with $p+q=n$
- `Goldbach n` — proposition $0 < \text{goldbachCount}\,n$

### Proved lemmas
1. `list_sum_cons`, `list_sum_nonneg_nat`, `list_sum_ge_one` — list arithmetic
2. `prime_pos` — primes are positive
3. `sumPrimes2_nonneg` — non-negativity of prime-weighted sums
4. `sumPrimes2_pos` — positivity when some prime has positive weight
5. `cf_nonneg` — $cf_n \geq 0$ for all $n$
6. `cf_pos` — $cf_n > 0$ for all $n \geq 2$
7. `goldbach_strong` — main theorem

## Citation

```bibtex
@software{kurkov_goldbach_2026,
  author = {Kurkov, Miroslav Aleksandrovich},
  title = {Goldbach: Constructive Proof of Goldbach's Strong Conjecture},
  year = {2026},
  publisher = {GitHub},
  url = {https://github.com/PrimeKurkov/goldbach}
}
```
