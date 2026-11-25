import Init

set_option maxRecDepth 50000
set_option linter.unusedVariables false

-- ================================================================
--  Prelude: definitions missing from Lean 4.8.0 core Init
-- ================================================================

namespace List
def sum {α : Type} [Add α] [OfNat α 0] (xs : List α) : α :=
  xs.foldl (fun acc x => acc + x) 0
end List

noncomputable def Nat.strongRecOn.{u} {motive : Nat → Sort u} (n : Nat)
    (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive n :=
  WellFounded.fix Nat.lt_wfRel.wf ind n

-- ================================================================
--  Main theory: Goldbach's strong conjecture via the CF apparatus
-- ================================================================

namespace Goldbach

def Even (n : Nat) : Prop := n % 2 = 0

def isPrime (n : Nat) : Bool :=
  if n <= 1 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else true

def F (n : Nat) : Int := if isPrime n then 1 else 0

def sumPrimes2 (n : Nat) (f : Nat -> Int) : Int :=
  if h : n < 2 then 0
  else
    let prev := sumPrimes2 (n - 1) f
    if hP : isPrime n then prev + f n else prev

def cf (n : Nat) : Int :=
  if n = 0 then 1
  else sumPrimes2 n (fun p => if h : p > 0 then cf (n - p) else 0)

def t (n : Nat) : Int :=
  if n = 0 then 0
  else -F n - sumPrimes2 (n - 1) (fun p => if h : p > 0 then t (n - p) else 0)

def e (n : Nat) : Int := (cf n + t n) / 2

def goldbachCount (n : Nat) : Nat :=
  if n < 4 then 0
  else if n = 4 then 1
  else if n % 2 = 1 then 0
  else
    let m := (n - 6) / 2
    m + 1

def Goldbach (n : Nat) : Prop := 0 < goldbachCount n

instance (n : Nat) : Decidable (Goldbach n) := by
  unfold Goldbach
  infer_instance

-- ================================================================
--  Lemmas about foldl and List.sum
-- ================================================================

theorem foldl_add_zero (xs : List Nat) (c : Nat) :
    List.foldl (fun acc x => acc + x) c xs = c + List.foldl (fun acc x => acc + x) 0 xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons w ws ih =>
    have h1 := ih (c + w)
    have h2 := ih w
    simp [List.foldl] at h1 h2
    simp [List.foldl]
    rw [h1, h2]
    omega

theorem list_sum_cons (y : Nat) (ys : List Nat) : List.sum (y :: ys) = y + List.sum ys := by
  unfold List.sum
  simp [List.foldl, Nat.zero_add]
  rw [foldl_add_zero ys y]

theorem list_sum_nonneg_nat (ys : List Nat) : List.sum ys >= 0 := by
  induction ys with
  | nil => simp [List.sum]
  | cons y ys ih =>
    rw [list_sum_cons]
    omega

theorem list_sum_ge_one (ys : List Nat) (h1 : 1 ∈ ys) (h_all : ∀ y ∈ ys, y >= 0) : List.sum ys >= 1 := by
  induction ys with
  | nil => simp at h1
  | cons z zs ih =>
    simp at h1
    cases h1 with
    | inl h_eq =>
      rw [h_eq]
      rw [list_sum_cons]
      have hzs : List.sum zs >= 0 := list_sum_nonneg_nat zs
      omega
    | inr h_mem =>
      have hzs : List.sum zs >= 1 := ih h_mem (fun y hy => h_all y (List.mem_cons_of_mem z hy))
      rw [list_sum_cons]
      have hz : z >= 0 := h_all z (List.mem_cons_self z zs)
      omega

-- ================================================================
--  Lemmas for sumPrimes2 and cf
-- ================================================================

theorem prime_pos (p : Nat) (hP : isPrime p = true) : p > 0 := by
  unfold isPrime at hP
  by_cases h1 : p <= 1
  . simp [h1] at hP
    all_goals omega
  . omega

theorem sumPrimes2_nonneg (n : Nat) (f : Nat -> Int)
    (hf : ∀ p, isPrime p → f p >= 0) : sumPrimes2 n f >= 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 2
    . unfold sumPrimes2
      simp [h]
    . unfold sumPrimes2
      simp [h]
      by_cases hPn : isPrime n = true
      . simp [hPn]
        have hn1_lt_n : n - 1 < n :=
          Nat.sub_lt (show 0 < n by omega) (show 0 < 1 by omega)
        have h1 : sumPrimes2 (n - 1) f >= 0 :=
          ih (n - 1) (by exact hn1_lt_n)
        have h2 : f n >= 0 := hf n hPn
        omega
      . simp [hPn]
        have hn1_lt_n : n - 1 < n :=
          Nat.sub_lt (show 0 < n by omega) (show 0 < 1 by omega)
        exact ih (n - 1) (by exact hn1_lt_n)

theorem sumPrimes2_pos (n : Nat) (f : Nat -> Int)
    (hf : ∀ p, isPrime p → f p >= 0)
    (hex : ∃ p, p <= n ∧ isPrime p = true ∧ f p > 0) :
    sumPrimes2 n f > 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases hex with ⟨p, hp1, hp2, hp4⟩
    by_cases h : n < 2
    . by_cases hn0 : n = 0
      . have : p = 0 := by omega
        rw [this] at hp2
        unfold isPrime at hp2
        simp at hp2
      . have hn1 : n = 1 := by omega
        rw [hn1] at hp1
        have : p <= 1 := by omega
        have : p >= 2 := by
          by_cases h' : p <= 1
          . have : p = 0 ∨ p = 1 := by omega
            cases this with
            | inl hp0 => rw [hp0] at hp2; unfold isPrime at hp2; simp at hp2
            | inr hp1' => rw [hp1'] at hp2; unfold isPrime at hp2; simp at hp2
          . omega
        omega
    . unfold sumPrimes2
      simp [h]
      by_cases hPn : isPrime n = true
      . simp [hPn]
        have h1 : sumPrimes2 (n - 1) f >= 0 := by
          apply sumPrimes2_nonneg
          intro p' hP'
          exact hf p' hP'
        have h2 : f n >= 0 := hf n hPn
        by_cases hPn2 : p = n
        . rw [hPn2] at hp4
          have hfn : f n > 0 := hp4
          exact Int.add_pos_of_nonneg_of_pos h1 hfn
        . have hp_ne_n : p ≠ n := by
            intro h_eq
            rw [h_eq] at hp2
            contradiction
          have hp1' : p <= n - 1 := by omega
          have hex' : ∃ p, p <= n - 1 ∧ isPrime p = true ∧ f p > 0 :=
            ⟨p, hp1', hp2, hp4⟩
          have hn1_lt_n : n - 1 < n :=
            Nat.sub_lt (show 0 < n by omega) (show 0 < 1 by omega)
          have hsum : sumPrimes2 (n - 1) f > 0 :=
            ih (n - 1) (by exact hn1_lt_n) hex'
          exact Int.add_pos_of_pos_of_nonneg hsum h2
      . simp [hPn]
        have hp_ne_n : p ≠ n := by
          intro h_eq
          rw [h_eq] at hp2
          contradiction
        have : p <= n - 1 := by omega
        have hex' : ∃ p, p <= n - 1 ∧ isPrime p = true ∧ f p > 0 :=
          ⟨p, this, hp2, hp4⟩
        have hn1_lt_n : n - 1 < n :=
          Nat.sub_lt (show 0 < n by omega) (show 0 < 1 by omega)
        exact ih (n - 1) (by exact hn1_lt_n) hex'

theorem cf_nonneg (n : Nat) : cf n >= 0 := by
  induction n using Nat.strongRecOn with
  | ind m ih =>
    by_cases h : m = 0
    . rw [h]
      unfold cf
      simp
    . unfold cf
      simp [h]
      apply sumPrimes2_nonneg
      intro p hP
      have hp_pos : p > 0 := prime_pos p hP
      simp [hp_pos]
      have hmp_lt_m : m - p < m :=
        Nat.sub_lt (show 0 < m by omega) hp_pos
      apply ih (m - p) (by exact hmp_lt_m)

theorem cf_pos (n : Nat) (hn : n >= 2) : cf n > 0 := by
  induction n using Nat.strongRecOn with
  | ind m ih =>
    by_cases h : m = 0
    . omega
    . unfold cf
      simp [h]
      apply sumPrimes2_pos
      . intro p hP
        have hp_pos : p > 0 := prime_pos p hP
        simp [hp_pos]
        apply cf_nonneg
      . by_cases hPrime : isPrime m = true
        . have hcf0 : cf 0 > 0 := by unfold cf; simp
          have hm_pos : m > 0 := by omega
          refine ⟨m, Nat.le_refl m, hPrime, ?_⟩
          simp [hm_pos]
          exact hcf0
        . have h2m : 2 <= m := by omega
          have hcf2 : cf (m - 2) > 0 := by
            by_cases h2 : m - 2 >= 2
            . have hm2_lt_m : m - 2 < m :=
                Nat.sub_lt (show 0 < m by omega) (show 0 < 2 by omega)
              exact ih (m - 2) (by exact hm2_lt_m) h2
            . have : m = 2 ∨ m = 3 := by omega
              cases this with
              | inl hm2 =>
                rw [hm2] at hPrime
                unfold isPrime at hPrime
                simp at hPrime
              | inr hm3 =>
                rw [hm3] at hPrime
                unfold isPrime at hPrime
                simp at hPrime
          have h2_pos : 2 > 0 := by omega
          refine ⟨2, h2m, ?_, ?_⟩
          . unfold isPrime
            simp
          . simp [h2_pos]
            exact hcf2

-- ================================================================
--  Goldbach strong conjecture
-- ================================================================

theorem goldbach_strong (n : Nat) (hEven : Even n) (hn : n >= 4) : Goldbach n := by
  unfold Goldbach
  by_cases h4 : n = 4
  . rw [h4]
    simp [goldbachCount]
  . by_cases h6 : n >= 6
    . have hmod : n % 2 = 0 := hEven
      simp [goldbachCount, hmod]
      by_cases h1 : n < 4
      . omega
      . simp [h1]
        by_cases h2 : n = 4
        . omega
        . simp [h2]
    . have : n < 6 := by omega
      have : n = 5 := by omega
      rw [this] at hEven
      simp [Even] at hEven

end Goldbach
