import Mathlib
import FormalConjectures.ErdosProblems.«1004»

/-!
# Collision and first-moment API for Erdős problem 1004

A run fails exactly when two different integers in its interval have the same
Euler totient. This file converts that observation into a finite covering
problem indexed by the shift `h`, proves the corresponding weighted union
bound, and exposes sufficient interfaces for both the positive and negative
forms of Erdős problem 1004.

The final sections record the Graham--Holt--Pomerance same-support affine
family, including its classical shift-two specialization, and connect those
collisions directly to the run predicate used by the target.
-/

open Filter Real Nat

namespace Contribution.Erdos1004Collision

section CollisionCore

/-- The equal-totient pair `(m, m + h)` lies in the run interval
`[n + 1, n + K]`. -/
def CollisionSpoils (m h n K : ℕ) : Prop :=
  n + 1 ≤ m ∧ m + h ≤ n + K

/-- A positive shifted equal-totient pair occurs inside the run interval. -/
def HasShiftedTotientCollision (n K : ℕ) : Prop :=
  ∃ m h : ℕ, 0 < h ∧ CollisionSpoils m h n K ∧
    m.totient = (m + h).totient

/-- The target's injectivity predicate is exactly absence of a shifted collision. -/
theorem isDistinctTotientRun_iff_not_hasShiftedTotientCollision (n K : ℕ) :
    Erdos1004.IsDistinctTotientRun n K ↔
      ¬HasShiftedTotientCollision n K := by
  constructor
  · intro hrun hcollision
    rcases hcollision with ⟨m, h, hh, ⟨hm_lower, hmh_upper⟩, htotient⟩
    have hm_mem : m ∈ Set.Icc (n + 1) (n + K) := by
      constructor <;> omega
    have hmh_mem : m + h ∈ Set.Icc (n + 1) (n + K) := by
      constructor <;> omega
    have heq : m = m + h := hrun hm_mem hmh_mem htotient
    omega
  · intro hnone
    rw [Erdos1004.IsDistinctTotientRun]
    intro a ha b hb htotient
    by_contra hab
    rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
    · apply hnone
      refine ⟨a, b - a, Nat.sub_pos_of_lt hab_lt, ⟨ha.1, ?_⟩, ?_⟩
      · simpa [Nat.add_sub_of_le hab_lt.le] using hb.2
      · simpa [Nat.add_sub_of_le hab_lt.le] using htotient
    · apply hnone
      refine ⟨b, a - b, Nat.sub_pos_of_lt hba_lt, ⟨hb.1, ?_⟩, ?_⟩
      · simpa [Nat.add_sub_of_le hba_lt.le] using ha.2
      · simpa [Nat.add_sub_of_le hba_lt.le] using htotient.symm

/-- The starts spoiled by `(m,m+h)` form the integer interval
`[m+h-K,m)`, with truncated subtraction at zero. -/
theorem collisionSpoils_iff_start_mem (m h n K : ℕ) :
    CollisionSpoils m h n K ↔ m + h - K ≤ n ∧ n < m := by
  unfold CollisionSpoils
  omega

/-- Any shifted pair fitting in a length-`K` run has shift strictly below `K`. -/
theorem shift_lt_runLength_of_collisionSpoils {m h n K : ℕ}
    (hspoil : CollisionSpoils m h n K) : h < K := by
  unfold CollisionSpoils at hspoil
  omega

end CollisionCore

section FiniteCover

/-- Candidate run starts up to `x`. -/
def candidateStarts (x : ℕ) : Finset ℕ := Finset.Icc 0 x

@[simp]
theorem mem_candidateStarts {x n : ℕ} : n ∈ candidateStarts x ↔ n ≤ x := by
  simp [candidateStarts]

@[simp]
theorem card_candidateStarts (x : ℕ) : (candidateStarts x).card = x + 1 := by
  simp [candidateStarts]

/-- Integers `m ∈ [1,X]` for which `φ(m)=φ(m+h)`. -/
def shiftedTotientCollisionSet (X h : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun m ↦ m.totient = (m + h).totient

/-- The exact shifted equal-totient counting function. -/
def shiftedTotientCollisionCount (X h : ℕ) : ℕ :=
  (shiftedTotientCollisionSet X h).card

@[simp]
theorem mem_shiftedTotientCollisionSet {X h m : ℕ} :
    m ∈ shiftedTotientCollisionSet X h ↔
      1 ≤ m ∧ m ≤ X ∧ m.totient = (m + h).totient := by
  simp [shiftedTotientCollisionSet, and_assoc]

/-- Candidate starts up to `x` spoiled by one fixed shifted collision. -/
def spoiledStarts (x K m h : ℕ) : Finset ℕ :=
  (candidateStarts x).filter fun n ↦
    n + 1 ≤ m ∧ m + h ≤ n + K

@[simp]
theorem mem_spoiledStarts {x K m h n : ℕ} :
    n ∈ spoiledStarts x K m h ↔
      n ≤ x ∧ CollisionSpoils m h n K := by
  simp [spoiledStarts, CollisionSpoils]

/-- All starts up to `x` spoiled by some positive shift below `K`.
Only collision left endpoints up to `x+K` can be relevant. -/
def collisionCoveredStarts (x K : ℕ) : Finset ℕ :=
  (Finset.Ico 1 K).biUnion fun h ↦
    (shiftedTotientCollisionSet (x + K) h).biUnion fun m ↦
      spoiledStarts x K m h

/-- Membership in the collision cover is exactly failure of the distinct-run
condition through a shifted collision. -/
theorem mem_collisionCoveredStarts_iff {x K n : ℕ} :
    n ∈ collisionCoveredStarts x K ↔
      n ≤ x ∧ HasShiftedTotientCollision n K := by
  classical
  constructor
  · intro hn
    rw [collisionCoveredStarts] at hn
    obtain ⟨h, hh, hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨m, hm, hn⟩ := Finset.mem_biUnion.mp hn
    have hh_data := Finset.mem_Ico.mp hh
    have hm_data := mem_shiftedTotientCollisionSet.mp hm
    have hn_data := mem_spoiledStarts.mp hn
    exact ⟨hn_data.1, m, h, by omega, hn_data.2, hm_data.2.2⟩
  · rintro ⟨hnx, m, h, hh, hspoil, htotient⟩
    have hhK : h < K := shift_lt_runLength_of_collisionSpoils hspoil
    have hm_lower : 1 ≤ m := by
      unfold CollisionSpoils at hspoil
      omega
    have hm_upper : m ≤ x + K := by
      unfold CollisionSpoils at hspoil
      omega
    rw [collisionCoveredStarts]
    apply Finset.mem_biUnion.mpr
    refine ⟨h, Finset.mem_Ico.mpr ⟨by omega, hhK⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨m, mem_shiftedTotientCollisionSet.mpr
      ⟨hm_lower, hm_upper, htotient⟩, ?_⟩
    exact mem_spoiledStarts.mpr ⟨hnx, hspoil⟩

/-- Every collision-covered start is a candidate start. -/
theorem collisionCoveredStarts_subset_candidateStarts (x K : ℕ) :
    collisionCoveredStarts x K ⊆ candidateStarts x := by
  intro n hn
  exact mem_candidateStarts.mpr (mem_collisionCoveredStarts_iff.mp hn).1

/-- Starts up to `x` whose totient run of length `K` is distinct. -/
def distinctTotientRunStarts (x K : ℕ) : Finset ℕ :=
  candidateStarts x \ collisionCoveredStarts x K

@[simp]
theorem mem_distinctTotientRunStarts {x K n : ℕ} :
    n ∈ distinctTotientRunStarts x K ↔
      n ≤ x ∧ Erdos1004.IsDistinctTotientRun n K := by
  rw [distinctTotientRunStarts, Finset.mem_sdiff, mem_candidateStarts,
    mem_collisionCoveredStarts_iff,
    isDistinctTotientRun_iff_not_hasShiftedTotientCollision]
  tauto

/-- The good starts are exactly the complement of the collision cover among
candidate starts. -/
theorem distinctTotientRunStarts_eq_sdiff_collisionCoveredStarts (x K : ℕ) :
    distinctTotientRunStarts x K =
      candidateStarts x \ collisionCoveredStarts x K := rfl

/-- One collision with shift `h` spoils at most `K-h` starts. -/
theorem spoiledStarts_card_le (x K m h : ℕ) :
    (spoiledStarts x K m h).card ≤ K - h := by
  have hsubset : spoiledStarts x K m h ⊆ Finset.Ico (m + h - K) m := by
    intro n hn
    exact Finset.mem_Ico.mpr
      ((collisionSpoils_iff_start_mem m h n K).mp
        (mem_spoiledStarts.mp hn).2)
  calc
    (spoiledStarts x K m h).card ≤
        (Finset.Ico (m + h - K) m).card := Finset.card_le_card hsubset
    _ = m - (m + h - K) := by simp
    _ ≤ K - h := by omega

/-- The first-moment quantity obtained by counting spoiled starts with
multiplicity over all positive shifts below `K`. -/
def weightedCollisionSum (x K : ℕ) : ℕ :=
  ∑ h ∈ Finset.Ico 1 K,
    (K - h) * shiftedTotientCollisionCount (x + K) h

/-- Finite union bound for starts spoiled by shifted equal-totient pairs. -/
theorem collisionCoveredStarts_card_le_weightedCollisionSum (x K : ℕ) :
    (collisionCoveredStarts x K).card ≤ weightedCollisionSum x K := by
  classical
  unfold collisionCoveredStarts weightedCollisionSum
  calc
    ((Finset.Ico 1 K).biUnion fun h ↦
        (shiftedTotientCollisionSet (x + K) h).biUnion fun m ↦
          spoiledStarts x K m h).card
        ≤ ∑ h ∈ Finset.Ico 1 K,
            ((shiftedTotientCollisionSet (x + K) h).biUnion fun m ↦
              spoiledStarts x K m h).card := Finset.card_biUnion_le
    _ ≤ ∑ h ∈ Finset.Ico 1 K,
          ∑ m ∈ shiftedTotientCollisionSet (x + K) h,
            (spoiledStarts x K m h).card := by
      exact Finset.sum_le_sum fun _h _hh ↦ Finset.card_biUnion_le
    _ ≤ ∑ h ∈ Finset.Ico 1 K,
          ∑ _m ∈ shiftedTotientCollisionSet (x + K) h,
            (K - h) := by
      exact Finset.sum_le_sum fun h _hh ↦
        Finset.sum_le_sum fun m _hm ↦ spoiledStarts_card_le x K m h
    _ = ∑ h ∈ Finset.Ico 1 K,
          (K - h) * shiftedTotientCollisionCount (x + K) h := by
      apply Finset.sum_congr rfl
      intro h hh
      simp [shiftedTotientCollisionCount, Nat.mul_comm]

/-- Exact cardinality of good starts in terms of the collision cover. -/
theorem distinctTotientRunStarts_card_eq (x K : ℕ) :
    (distinctTotientRunStarts x K).card =
      x + 1 - (collisionCoveredStarts x K).card := by
  rw [distinctTotientRunStarts_eq_sdiff_collisionCoveredStarts,
    Finset.card_sdiff_of_subset
      (collisionCoveredStarts_subset_candidateStarts x K),
    card_candidateStarts]

/-- Quantitative first-moment lower bound for the number of distinct-run starts. -/
theorem weightedCollisionSum_lower_bound_good_starts (x K : ℕ) :
    x + 1 - weightedCollisionSum x K ≤
      (distinctTotientRunStarts x K).card := by
  have hcover := collisionCoveredStarts_card_le_weightedCollisionSum x K
  have hcard := distinctTotientRunStarts_card_eq x K
  omega

/-- If the weighted collision count is below the number of candidate starts,
then at least one desired run exists. -/
theorem exists_isDistinctTotientRun_of_weightedCollisionSum_lt
    {x K : ℕ} (hsmall : weightedCollisionSum x K < x + 1) :
    ∃ n ≤ x, Erdos1004.IsDistinctTotientRun n K := by
  have hpositive : 0 < (distinctTotientRunStarts x K).card := by
    have hlower := weightedCollisionSum_lower_bound_good_starts x K
    omega
  rw [Finset.card_pos] at hpositive
  obtain ⟨n, hn⟩ := hpositive
  rcases mem_distinctTotientRunStarts.mp hn with ⟨hnx, hrun⟩
  exact ⟨n, hnx, hrun⟩

/-- If every candidate run fails, the first-moment quantity must be at least
`x+1`. -/
theorem weightedCollisionSum_ge_of_all_runs_fail {x K : ℕ}
    (hfail : ∀ n ≤ x, ¬Erdos1004.IsDistinctTotientRun n K) :
    x + 1 ≤ weightedCollisionSum x K := by
  by_contra hnot
  have hsmall : weightedCollisionSum x K < x + 1 := by omega
  obtain ⟨n, hn, hrun⟩ :=
    exists_isDistinctTotientRun_of_weightedCollisionSum_lt hsmall
  exact hfail n hn hrun

end FiniteCover

section GHPDiagonal

/-- The finite set of prime divisors of `n`. -/
abbrev primeSupport (n : ℕ) : Finset ℕ := n.primeFactors

/-- The same-support index condition underlying the
Graham--Holt--Pomerance diagonal. -/
def IsSameSupportIndex (h j : ℕ) : Prop :=
  1 ≤ j ∧ primeSupport j = primeSupport (j + h)

/-- The common divisor of `j` and `j+h`. -/
def diagonalGCD (h j : ℕ) : ℕ := Nat.gcd j (j + h)

/-- The reduced numerator `(j+h)/gcd(j,j+h)`. -/
def diagonalA (h j : ℕ) : ℕ := (j + h) / diagonalGCD h j

/-- The reduced denominator `j/gcd(j,j+h)`. -/
def diagonalB (h j : ℕ) : ℕ := j / diagonalGCD h j

/-- The left integer in the same-support affine family. -/
def ghpLeft (h j r : ℕ) : ℕ := j * (diagonalA h j * r + 1)

/-- The right integer in the same-support affine family. -/
def ghpRight (h j r : ℕ) : ℕ :=
  (j + h) * (diagonalB h j * r + 1)

/-- All arithmetic hypotheses making the same-support affine pair a genuine
pair of equal totients. -/
def IsGHPParameter (h j r : ℕ) : Prop :=
  IsSameSupportIndex h j ∧
    Nat.Prime (diagonalA h j * r + 1) ∧
    Nat.Prime (diagonalB h j * r + 1) ∧
    Nat.Coprime (diagonalA h j * r + 1) j ∧
    Nat.Coprime (diagonalB h j * r + 1) (j + h)

theorem diagonalGCD_dvd_left (h j : ℕ) : diagonalGCD h j ∣ j := by
  exact Nat.gcd_dvd_left j (j + h)

theorem diagonalGCD_dvd_right (h j : ℕ) : diagonalGCD h j ∣ j + h := by
  exact Nat.gcd_dvd_right j (j + h)

theorem diagonalGCD_mul_diagonalB (h j : ℕ) :
    diagonalGCD h j * diagonalB h j = j := by
  rw [mul_comm]
  exact Nat.div_mul_cancel (diagonalGCD_dvd_left h j)

theorem diagonalGCD_mul_diagonalA (h j : ℕ) :
    diagonalGCD h j * diagonalA h j = j + h := by
  rw [mul_comm]
  exact Nat.div_mul_cancel (diagonalGCD_dvd_right h j)

/-- The two affine descriptions have difference exactly `h`. -/
theorem ghpLeft_add_shift_eq_ghpRight (h j r : ℕ) :
    ghpLeft h j r + h = ghpRight h j r := by
  have hcross : (j + h) * diagonalB h j = j * diagonalA h j := by
    calc
      (j + h) * diagonalB h j =
          (diagonalGCD h j * diagonalA h j) * diagonalB h j := by
            rw [diagonalGCD_mul_diagonalA]
      _ = (diagonalGCD h j * diagonalB h j) * diagonalA h j := by
            ac_rfl
      _ = j * diagonalA h j := by rw [diagonalGCD_mul_diagonalB]
  unfold ghpLeft ghpRight
  calc
    j * (diagonalA h j * r + 1) + h =
        (j * diagonalA h j) * r + (j + h) := by ring
    _ = ((j + h) * diagonalB h j) * r + (j + h) := by rw [← hcross]
    _ = (j + h) * (diagonalB h j * r + 1) := by ring

/-- Equal prime support gives equal rational values of `φ(n)/n`. -/
theorem totient_div_eq_of_primeSupport_eq {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hsupport : primeSupport a = primeSupport b) :
    (a.totient : ℚ) / a = (b.totient : ℚ) / b := by
  rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors]
  rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr ha),
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hb)]
  simpa [primeSupport] using congrArg
    (fun support : Finset ℕ ↦ ∏ p ∈ support, (1 - (p : ℚ)⁻¹)) hsupport

/-- Integral cross-multiplied form of equal `φ(n)/n` ratios. -/
theorem totient_mul_eq_of_primeSupport_eq {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hsupport : primeSupport a = primeSupport b) :
    a.totient * b = b.totient * a := by
  have hratio := totient_div_eq_of_primeSupport_eq ha hb hsupport
  have hcross : (a.totient : ℚ) * (b : ℚ) =
      (b.totient : ℚ) * (a : ℚ) :=
    (div_eq_div_iff (Nat.cast_ne_zero.mpr ha)
      (Nat.cast_ne_zero.mpr hb)).mp hratio
  apply Nat.cast_injective (R := ℚ)
  simpa only [Nat.cast_mul] using hcross

/-- Same support identifies the totient coefficients of the reduced ratio. -/
theorem totient_mul_diagonalA_eq_totient_mul_diagonalB
    {h j : ℕ} (hsame : IsSameSupportIndex h j) :
    j.totient * diagonalA h j =
      (j + h).totient * diagonalB h j := by
  obtain ⟨hjpos, hsupport⟩ := hsame
  have hjne : j ≠ 0 := by omega
  have hjhne : j + h ≠ 0 := by omega
  have hcross : j.totient * (j + h) = (j + h).totient * j :=
    totient_mul_eq_of_primeSupport_eq hjne hjhne hsupport
  have hdpos : 0 < diagonalGCD h j := by
    exact Nat.gcd_pos_of_pos_left (j + h) hjpos
  apply Nat.mul_left_cancel hdpos
  calc
    diagonalGCD h j * (j.totient * diagonalA h j) =
        j.totient * (diagonalGCD h j * diagonalA h j) := by ac_rfl
    _ = j.totient * (j + h) := by rw [diagonalGCD_mul_diagonalA]
    _ = (j + h).totient * j := hcross
    _ = (j + h).totient * (diagonalGCD h j * diagonalB h j) := by
          rw [diagonalGCD_mul_diagonalB]
    _ = diagonalGCD h j *
        ((j + h).totient * diagonalB h j) := by ac_rfl

/-- Every valid same-support affine parameter gives equal totients. -/
theorem ghp_totient_eq {h j r : ℕ} (hparam : IsGHPParameter h j r) :
    (ghpLeft h j r).totient = (ghpRight h j r).totient := by
  rcases hparam with ⟨hsame, hprimeA, hprimeB, hcoprimeA, hcoprimeB⟩
  unfold ghpLeft ghpRight
  rw [Nat.totient_mul hcoprimeA.symm,
    Nat.totient_mul hcoprimeB.symm,
    Nat.totient_prime hprimeA, Nat.totient_prime hprimeB]
  simp only [Nat.add_sub_cancel]
  calc
    j.totient * (diagonalA h j * r) =
        (j.totient * diagonalA h j) * r := by ring
    _ = ((j + h).totient * diagonalB h j) * r := by
          rw [totient_mul_diagonalA_eq_totient_mul_diagonalB hsame]
    _ = (j + h).totient * (diagonalB h j * r) := by ring

/-- A valid same-support affine parameter is a collision of shift `h`. -/
theorem ghp_hasShiftedTotientCollision {h j r n K : ℕ}
    (hh : 0 < h) (hparam : IsGHPParameter h j r)
    (hspoil : CollisionSpoils (ghpLeft h j r) h n K) :
    HasShiftedTotientCollision n K := by
  refine ⟨ghpLeft h j r, h, hh, hspoil, ?_⟩
  rw [ghpLeft_add_shift_eq_ghpRight]
  exact ghp_totient_eq hparam

/-- A run containing a valid same-support affine pair cannot be distinct. -/
theorem not_isDistinctTotientRun_of_ghp {h j r n K : ℕ}
    (hh : 0 < h) (hparam : IsGHPParameter h j r)
    (hspoil : CollisionSpoils (ghpLeft h j r) h n K) :
    ¬Erdos1004.IsDistinctTotientRun n K := by
  rw [isDistinctTotientRun_iff_not_hasShiftedTotientCollision]
  exact not_not_intro
    (ghp_hasShiftedTotientCollision hh hparam hspoil)

/-- A valid GHP left endpoint below `X` belongs to the exact shifted-collision set. -/
theorem ghpLeft_mem_shiftedTotientCollisionSet {X h j r : ℕ}
    (hh : 0 < h) (hparam : IsGHPParameter h j r)
    (hX : ghpLeft h j r ≤ X) :
    ghpLeft h j r ∈ shiftedTotientCollisionSet X h := by
  have hj : 1 ≤ j := hparam.1.1
  have hleft_pos : 0 < ghpLeft h j r := by
    unfold ghpLeft
    exact Nat.mul_pos (by omega) (Nat.succ_pos _)
  apply mem_shiftedTotientCollisionSet.mpr
  refine ⟨hleft_pos, hX, ?_⟩
  rw [ghpLeft_add_shift_eq_ghpRight]
  exact ghp_totient_eq hparam

end GHPDiagonal

section ClassicalShiftTwo

/-- Left endpoint of the classical shift-two family. -/
def classicalHTwoLeft (t : ℕ) : ℕ := 2 * (4 * t + 1)

/-- The classical pair `2(4t+1), 4(2t+1)` is a valid same-support
Graham--Holt--Pomerance parameter. -/
theorem classical_h_two_isGHPParameter {t : ℕ}
    (hp : Nat.Prime (2 * t + 1))
    (hq : Nat.Prime (4 * t + 1)) :
    IsGHPParameter 2 2 (2 * t) := by
  have hA : diagonalA 2 2 = 2 := by
    norm_num [diagonalA, diagonalGCD]
  have hB : diagonalB 2 2 = 1 := by
    norm_num [diagonalB, diagonalGCD]
  have hoddq : Odd (4 * t + 1) := ⟨2 * t, by omega⟩
  have hoddp : Odd (2 * t + 1) := ⟨t, by omega⟩
  have hcoprimeP4 : Nat.Coprime (2 * t + 1) 4 := by
    rw [show 4 = 2 ^ 2 by norm_num,
      Nat.coprime_pow_right_iff (by norm_num)]
    exact hoddp.coprime_two_right
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, ?_⟩
    change Nat.primeFactors 2 = Nat.primeFactors 4
    simpa using
      (Nat.primeFactors_pow 2 (k := 2) (by norm_num)).symm
  · rw [hA]
    convert hq using 1 <;> omega
  · rw [hB]
    simpa using hp
  · rw [hA]
    convert hoddq.coprime_two_right using 1 <;> omega
  · rw [hB]
    simpa using hcoprimeP4

/-- The classical shift-two family gives an exact equal-totient identity. -/
theorem classical_h_two_totient_eq {t : ℕ}
    (hp : Nat.Prime (2 * t + 1))
    (hq : Nat.Prime (4 * t + 1)) :
    (classicalHTwoLeft t).totient =
      (classicalHTwoLeft t + 2).totient := by
  have hparam := classical_h_two_isGHPParameter hp hq
  have heq := ghp_totient_eq hparam
  have hshift := ghpLeft_add_shift_eq_ghpRight 2 2 (2 * t)
  have hleft : ghpLeft 2 2 (2 * t) = classicalHTwoLeft t := by
    norm_num [ghpLeft, classicalHTwoLeft, diagonalA, diagonalGCD]
    ring
  rw [hleft] at hshift heq
  rw [hshift]
  exact heq

/-- A run start is covered by the classical shift-two family. -/
def ClassicalHTwoCoversStart (n K : ℕ) : Prop :=
  ∃ t : ℕ, Nat.Prime (2 * t + 1) ∧ Nat.Prime (4 * t + 1) ∧
    CollisionSpoils (classicalHTwoLeft t) 2 n K

/-- Classical shift-two coverage supplies an actual shifted collision. -/
theorem hasShiftedTotientCollision_of_classicalHTwoCoversStart {n K : ℕ}
    (hcover : ClassicalHTwoCoversStart n K) :
    HasShiftedTotientCollision n K := by
  rcases hcover with ⟨t, hp, hq, hspoil⟩
  exact ⟨classicalHTwoLeft t, 2, by norm_num, hspoil,
    classical_h_two_totient_eq hp hq⟩

/-- Any start covered by the classical family fails the target run predicate. -/
theorem not_isDistinctTotientRun_of_classicalHTwoCoversStart {n K : ℕ}
    (hcover : ClassicalHTwoCoversStart n K) :
    ¬Erdos1004.IsDistinctTotientRun n K := by
  rw [isDistinctTotientRun_iff_not_hasShiftedTotientCollision]
  exact not_not_intro
    (hasShiftedTotientCollision_of_classicalHTwoCoversStart hcover)

end ClassicalShiftTwo

section TargetInterfaces

/-- The run length occurring in the exact Erdős 1004 statement. -/
noncomputable def requestedRunLength (x : ℕ) (c : ℝ) : ℕ :=
  ⌊(Real.log (x : ℝ)) ^ c⌋₊

/-- Every candidate start up to `x` contains a shifted equal-totient pair. -/
def AllStartsHaveCollision (x K : ℕ) : Prop :=
  ∀ n ≤ x, HasShiftedTotientCollision n K

/-- Every candidate start up to `x` is covered by the classical shift-two family. -/
def AllStartsCoveredByClassicalHTwo (x K : ℕ) : Prop :=
  ∀ n ≤ x, ClassicalHTwoCoversStart n K

/-- Local failure of every run is exactly collision coverage of every start. -/
theorem no_distinct_run_iff_allStartsHaveCollision (x K : ℕ) :
    (¬∃ n ≤ x, Erdos1004.IsDistinctTotientRun n K) ↔
      AllStartsHaveCollision x K := by
  constructor
  · intro hnone n hn
    by_contra hcollision
    apply hnone
    exact ⟨n, hn,
      (isDistinctTotientRun_iff_not_hasShiftedTotientCollision n K).mpr
        hcollision⟩
  · intro hall hrun
    rcases hrun with ⟨n, hn, hdistinct⟩
    exact (isDistinctTotientRun_iff_not_hasShiftedTotientCollision n K).mp
      hdistinct (hall n hn)

/-- The weighted first-moment estimate is a complete sufficient analytic
interface for the positive direction of Erdős 1004. -/
theorem erdos_1004_of_eventually_weightedCollisionSum_lt
    (hbound : ∀ c > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      weightedCollisionSum x (requestedRunLength x c) < x + 1) :
    True ↔ ∀ c > (0 : ℝ), ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
      Erdos1004.IsDistinctTotientRun n (requestedRunLength x c) := by
  constructor
  · intro _ c hc
    filter_upwards [hbound c hc] with x hx
    exact exists_isDistinctTotientRun_of_weightedCollisionSum_lt hx
  · intro _
    trivial

/-- Frequently covering every start at one positive exponent is a complete
sufficient interface for refuting the Erdős 1004 assertion. -/
theorem erdos_1004_false_of_frequently_allStartsHaveCollision
    {c : ℝ} (hc : 0 < c)
    (hfrequent : ∃ᶠ x : ℕ in atTop,
      AllStartsHaveCollision x (requestedRunLength x c)) :
    ¬(True ↔ ∀ d > (0 : ℝ), ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
      Erdos1004.IsDistinctTotientRun n (requestedRunLength x d)) := by
  intro htarget
  have heventual := htarget.mp trivial c hc
  apply hfrequent
  filter_upwards [heventual] with x hx
  intro hall
  rcases hx with ⟨n, hn, hrun⟩
  exact (isDistinctTotientRun_iff_not_hasShiftedTotientCollision
    n (requestedRunLength x c)).mp hrun (hall n hn)

/-- Classical shift-two coverage implies general collision coverage. -/
theorem allStartsHaveCollision_of_allStartsCoveredByClassicalHTwo
    {x K : ℕ} (hcover : AllStartsCoveredByClassicalHTwo x K) :
    AllStartsHaveCollision x K := by
  intro n hn
  exact hasShiftedTotientCollision_of_classicalHTwoCoversStart
    (hcover n hn)

/-- A local prime-pair coverage theorem for the classical shift-two family
would refute the exact Erdős 1004 assertion. -/
theorem erdos_1004_false_of_frequently_classicalHTwoCoverage
    {c : ℝ} (hc : 0 < c)
    (hfrequent : ∃ᶠ x : ℕ in atTop,
      AllStartsCoveredByClassicalHTwo x (requestedRunLength x c)) :
    ¬(True ↔ ∀ d > (0 : ℝ), ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
      Erdos1004.IsDistinctTotientRun n (requestedRunLength x d)) := by
  apply erdos_1004_false_of_frequently_allStartsHaveCollision hc
  exact hfrequent.mono fun _x hx ↦
    allStartsHaveCollision_of_allStartsCoveredByClassicalHTwo hx

end TargetInterfaces

end Contribution.Erdos1004Collision
