import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! Integer certificates for the range between the residue count and the uniform tail.

The rank thresholds record powers of two gained over the factorial bound.
A Fermat test gives the initial prime count bound. The first intervals use
divisor witnesses on a wheel modulo 210, with 10 bits per candidate. The
subsequent intervals use the dyadic estimate from the primorial.
-/

namespace Erdos137OddBridge

open Finset

def rankBound (i : ℕ) : ℕ :=
  max i (max ((1260*(i-304)+352)/353) ((21701*(i-1492)+4999)/5000))

def retainedCount (k : ℕ) : ℕ := k - ((range k).filter Nat.Prime).card

lemma retained_count_mono : Monotone retainedCount := by
  have h (k : ℕ) : retainedCount k = ((range k).filter (fun p => ¬p.Prime)).card := by
    unfold retainedCount
    have hCount := card_filter_add_card_filter_not (s := range k) Nat.Prime
    rw [card_range] at hCount
    omega
  intro k m hm
  rw [h,h]
  exact card_le_card (filter_subset_filter _ (range_mono hm))

lemma rank_scaled_first (i : ℕ) : 1260*(i-304) ≤ 353*rankBound i := by
  have h : (1260*(i-304)+352)/353 ≤ rankBound i :=
    (le_max_left _ _).trans (le_max_right _ _)
  omega

lemma rank_scaled_second (i : ℕ) : 21701*(i-1492) ≤ 5000*rankBound i := by
  have h : (21701*(i-1492)+4999)/5000 ≤ rankBound i :=
    (le_max_right _ _).trans (le_max_right _ _)
  omega

lemma extend_rank_power {t i a b c j : ℕ} (ht : 0 < t) (hti : t ≤ i) (ha : a ≤ t)
    (hb : 0 < b) (hWitness : 2^j*(b*t)^64 ≤ (c*(t-a))^64)
    (hRank : c*(i-a) ≤ b*rankBound i) :
    2^j*i^64 ≤ (rankBound i)^64 := by
  have hSub : (t-a)*i ≤ (i-a)*t := by
    have hA := Nat.sub_add_cancel ha
    have hB := Nat.sub_add_cancel (ha.trans hti)
    have hProd := Nat.mul_le_mul_left a hti
    nlinarith
  have hSlope : c*(t-a)*i ≤ b*rankBound i*t :=
    (show c*(t-a)*i ≤ c*(i-a)*t by
      simpa only [mul_assoc] using Nat.mul_le_mul_left c hSub).trans (Nat.mul_le_mul_right t hRank)
  have hGoal : (b*t)^64*(2^j*i^64) ≤ (b*t)^64*(rankBound i)^64 := by
    calc
      _ = (2^j*(b*t)^64)*i^64 := by ac_rfl
      _ ≤ (c*(t-a))^64*i^64 := Nat.mul_le_mul_right _ hWitness
      _ = (c*(t-a)*i)^64 := by rw [← mul_pow]
      _ ≤ (b*rankBound i*t)^64 := pow_le_pow_left' hSlope _
      _ = _ := by rw [show b*rankBound i*t = b*t*rankBound i by ac_rfl, mul_pow]
  exact Nat.le_of_mul_le_mul_left hGoal (by positivity)

lemma rank_power_at {t i j : ℕ} (ht : 0 < t) (hti : t ≤ i)
    (hW : (304 ≤ t ∧ 2^j*(353*t)^64 ≤ (1260*(t-304))^64) ∨
      (1492 ≤ t ∧ 2^j*(5000*t)^64 ≤ (21701*(t-1492))^64)) :
    2^j*i^64 ≤ (rankBound i)^64 := by
  rcases hW with ⟨hA,hW⟩ | ⟨hA,hW⟩
  · exact extend_rank_power ht hti hA (by decide) hW (rank_scaled_first i)
  · exact extend_rank_power ht hti hA (by decide) hW (rank_scaled_second i)

def gainedExponent (thresholds : List ℕ) (r : ℕ) : ℕ :=
  (thresholds.map fun t => r-(t-1)).sum

lemma sum_rank_gains (thresholds : List ℕ) (r : ℕ) :
    gainedExponent thresholds r =
      ∑ i ∈ range r, (thresholds.filter fun t => t ≤ i+1).length := by
  have hCount (t : ℕ) : (∑ i ∈ range r, if t ≤ i+1 then (1:ℕ) else 0) = r-(t-1) := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    have hSet : (range r).filter (fun i => t ≤ i+1) = Ico (t-1) r := by
      ext i
      simp only [mem_filter,mem_range,mem_Ico]
      omega
    rw [hSet, Nat.card_Ico]
    simp
  induction thresholds with
  | nil => simp [gainedExponent]
  | cons t ts ih =>
    have hT := hCount t
    simp only [gainedExponent,List.map_cons,List.sum_cons] at ih ⊢
    have hStep (i : ℕ) : ((t::ts).filter fun v => v ≤ i+1).length =
        (if t ≤ i+1 then 1 else 0) + (ts.filter fun v => v ≤ i+1).length := by
      by_cases hti : t ≤ i+1 <;> simp [hti, Nat.add_comm]
    simp_rw [hStep,sum_add_distrib]
    rw [hT, ih]

def carriesRankPower (t j : ℕ) : Prop :=
  0 < t ∧ ((304 ≤ t ∧ 2^j*(353*t)^64 ≤ (1260*(t-304))^64) ∨
    (1492 ≤ t ∧ 2^j*(5000*t)^64 ≤ (21701*(t-1492))^64))

instance (t j : ℕ) : Decidable (carriesRankPower t j) := by
  unfold carriesRankPower
  infer_instance

def RankThresholds (thresholds : List ℕ) (offset : ℕ) : Prop := match thresholds with
  | [] => True
  | t :: ts => carriesRankPower t (offset+1) ∧ RankThresholds ts (offset+1)

instance (thresholds : List ℕ) (offset : ℕ) : Decidable (RankThresholds thresholds offset) := by
  induction thresholds generalizing offset with
  | nil => unfold RankThresholds; infer_instance
  | cons t ts ih =>
    unfold RankThresholds
    letI := ih (offset+1)
    infer_instance

lemma rank_power_of_thresholds (ts : List ℕ) (j i : ℕ) (hT : RankThresholds ts j)
    (hN : 0 < (ts.filter fun t => t ≤ i).length) :
    2^(j+(ts.filter fun t => t ≤ i).length)*i^64 ≤ (rankBound i)^64 := by
  induction ts generalizing j with
  | nil => simpa using hN
  | cons t ts ih =>
    obtain ⟨hW,hTs⟩ := hT
    let r := (ts.filter fun t => t ≤ i).length
    have hCount : ((t::ts).filter fun t => t ≤ i).length = (if t ≤ i then 1 else 0)+r := by
      by_cases h : t ≤ i <;> simp [h,r,Nat.add_comm]
    rw [hCount] at hN ⊢
    by_cases hR : 0 < r
    · apply (Nat.mul_le_mul_right (i^64) (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ?_)).trans
        (ih (j+1) hTs hR)
      split <;> omega
    · have hLE : t ≤ i := by
        by_contra hh
        rw [if_neg hh] at hN
        omega
      simp only [if_pos hLE, show r = 0 by omega, Nat.add_zero]
      exact rank_power_at hW.1 hLE hW.2

lemma rank_product_power (ts : List ℕ) (r : ℕ) (hT : RankThresholds ts 0) :
    2^(gainedExponent ts r)*(r.factorial)^64 ≤
      (∏ i ∈ range r, rankBound (i+1))^64 := by
  let g := fun i : ℕ => (ts.filter fun t => t ≤ i+1).length
  have hFact : (∏ i ∈ range r, (i+1)) = r.factorial := by
    induction r with
    | zero => simp
    | succ r ih => rw [prod_range_succ, ih, Nat.factorial_succ, Nat.mul_comm]
  rw [sum_rank_gains, ← Finset.prod_pow_eq_pow_sum, ← hFact, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  apply prod_le_prod'
  intro i _
  by_cases hi : 0 < g i
  · simpa only [g,Nat.zero_add] using rank_power_of_thresholds ts 0 (i+1) hT hi
  · simpa [g, show g i = 0 by omega] using
      (pow_le_pow_left' (show i+1 ≤ rankBound (i+1) from le_max_left _ _) 64)

lemma factorial_mul_bound (r d U : ℕ) (h : r+d ≤ U) :
    (r+d).factorial ≤ r.factorial*U^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show r+d.succ = r+d+1 by omega, Nat.factorial_succ,pow_succ]
    exact (Nat.mul_le_mul h (ih (by omega))).trans_eq (by ac_rfl)

lemma rank_product_on_interval (ts : List ℕ) (lo hi P B k : ℕ)
    (hT : RankThresholds ts 0) (hLo : 3 ≤ lo) (hk₁ : lo ≤ k) (hk₂ : k ≤ hi)
    (hCount : ((range lo).filter Nat.Prime).card ≤ P)
    (hBudget : (hi-1)^64 ≤ 2^B)
    (hGain : (hi-1-(lo-P))*B < gainedExponent ts (lo-P)) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  let r := lo-P
  have hrK : r ≤ retainedCount k := by
    apply le_trans _ (retained_count_mono hk₁)
    unfold retainedCount
    dsimp [r]
    omega
  have hProd := rank_product_power ts r hT
  by_cases hr : r ≤ hi-1
  · have hUpper : (k-1).factorial ≤ r.factorial*(hi-1)^(hi-1-r) := by
      apply (Nat.factorial_le (by omega : k-1 ≤ hi-1)).trans
      have h := factorial_mul_bound r (hi-1-r) (hi-1) (by omega)
      rwa [show r+(hi-1-r) = hi-1 by omega] at h
    have hRaised : ((k-1).factorial)^64 ≤ 2^((hi-1-r)*B)*(r.factorial)^64 := by
      calc
        _ ≤ (r.factorial*(hi-1)^(hi-1-r))^64 := pow_le_pow_left' hUpper _
        _ = ((hi-1)^64)^(hi-1-r)*(r.factorial)^64 := by
          rw [mul_pow, mul_comm]; congr 1
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ (2^B)^(hi-1-r)*(r.factorial)^64 :=
          Nat.mul_le_mul_right _ (pow_le_pow_left' hBudget _)
        _ = _ := by rw [← pow_mul, Nat.mul_comm B]
    have hL : ((k-1).factorial)^64 < (∏ i ∈ range r, rankBound (i+1))^64 :=
      hRaised.trans_lt ((Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) hGain)
        (by positivity)).trans_le hProd)
    exact (lt_of_pow_lt_pow_left' 64 hL).trans_le (prod_le_prod_of_subset_of_one_le'
      (range_mono hrK) (fun i _ _ => (Nat.succ_pos i).trans_le (le_max_left _ _)))
  · have hFac : (k-1).factorial < r.factorial :=
      Nat.factorial_lt_of_lt (by omega) (by omega)
    have hProd' : r.factorial ≤ ∏ i ∈ range r, rankBound (i+1) := by
      by_contra! h
      have hI := Nat.pow_lt_pow_left h (by decide : (64:ℕ) ≠ 0)
      exact (not_lt_of_ge ((Nat.le_mul_of_pos_left _ (by positivity)).trans hProd)) hI
    exact hFac.trans_le (hProd'.trans (prod_le_prod_of_subset_of_one_le'
      (range_mono hrK) (fun i _ _ => (Nat.succ_pos i).trans_le (le_max_left _ _))))

private def modPowByBits (a e m : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | fuel+1 =>
      if e = 0 then 1 % m else
        let next := modPowByBits (a*a%m) (e/2) m fuel
        if e%2 = 0 then next else a*next%m

private lemma mod_pow_by_bits_eq (a e m fuel : ℕ) (h : e < 2^fuel) :
    modPowByBits a e m fuel = a^e%m := by
  induction fuel generalizing a e with
  | zero =>
    have he : e = 0 := by simp at h; omega
    simp [modPowByBits,he]
  | succ fuel ih =>
    by_cases he : e = 0
    · simp [modPowByBits,he]
    have hHalf : e/2 < 2^fuel := by rw [pow_succ] at h; omega
    have hRest := ih (a*a%m) (e/2) hHalf
    have hRest' : (a*a%m)^(e/2)%m = a^(2*(e/2))%m := by
      rw [pow_mul, pow_two, ← Nat.pow_mod]
    simp only [modPowByBits,if_neg he,hRest,hRest']
    by_cases hEven : e%2 = 0
    · rw [if_pos hEven, show 2*(e/2) = e by omega]
    · rw [if_neg hEven]
      conv_rhs => rw [show e = 2*(e/2)+1 by omega, pow_succ' a]
      calc
        _ = (a%m*(a^(2*(e/2))%m))%m := by rw [Nat.mul_mod a, Nat.mod_mod]
        _ = _ := (Nat.mul_mod a _ m).symm

def fermatCandidate (n : ℕ) : Prop :=
  n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨
    (7 < n ∧ n.Coprime 210 ∧ modPowByBits 2 (n-1) n n.log2.succ = 1)

instance (n : ℕ) : Decidable (fermatCandidate n) := by
  unfold fermatCandidate
  infer_instance

lemma prime_is_fermat_candidate {p : ℕ} (hp : p.Prime) : fermatCandidate p := by
  by_cases h : p ≤ 7
  · interval_cases p <;> first | decide | exact False.elim ((show ¬Nat.Prime _ by decide) hp)
  unfold fermatCandidate
  right; right; right; right
  have hC : ∀ d : ℕ, 0 < d → d < p → p.Coprime d := fun d hd hd' =>
    (hp.coprime_iff_not_dvd).2 (fun hD => (not_le_of_gt hd') (Nat.le_of_dvd hd hD))
  have hSmall : p.Coprime 210 := by
    change p.Coprime (2*3*5*7)
    exact (((hC 2 (by decide) (by omega)).mul_right (hC 3 (by decide) (by omega))).mul_right
      (hC 5 (by decide) (by omega))).mul_right (hC 7 (by decide) (by omega))
  refine ⟨by omega,hSmall,?_⟩
  have hF : 2^(p-1)%p = 1%p := Nat.ModEq.pow_card_sub_one_eq_one hp (hC 2 (by decide) (by omega)).symm
  rw [mod_pow_by_bits_eq _ _ _ _ (by have := Nat.lt_log2_self (n := p); omega),
    hF, Nat.mod_eq_of_lt (by omega : 1 < p)]

def candidatePrefix (n : ℕ) : Finset ℕ := (range n).filter fermatCandidate

private def wheelResidues : List ℕ :=
  [1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
    103, 107, 109, 113, 121, 127, 131, 137, 139, 143, 149, 151, 157, 163, 167, 169, 173, 179, 181, 187, 191, 193, 197, 199, 209]

private lemma wheel_residues_exact :
    wheelResidues = (List.range 210).filter (fun r => decide (r.Coprime 210)) := by decide

private def possiblePrimesInBlock (lo hi q code : ℕ) : List ℕ → List ℕ
  | [] => []
  | r :: residues =>
      let n := 210*q+r
      let factor := code%1024
      let rest := possiblePrimesInBlock lo hi q (code/1024) residues
      if lo ≤ n ∧ n < hi ∧ ¬ (1 < factor ∧ factor < n ∧ factor ∣ n) then n :: rest else rest

private lemma prime_in_wheel_block {lo hi q r : ℕ} (residues : List ℕ) (code : ℕ)
    (hr : r ∈ residues) (hlo : lo ≤ 210*q+r) (hhi : 210*q+r < hi)
    (hp : (210*q+r).Prime) : 210*q+r ∈ possiblePrimesInBlock lo hi q code residues := by
  induction residues generalizing code with
  | nil => simp at hr
  | cons t rs ih =>
    rcases List.mem_cons.mp hr with ht | hr
    · subst t
      have hNo : ¬ (1 < code%1024 ∧ code%1024 < 210*q+r ∧ code%1024 ∣ 210*q+r) := by
        rintro ⟨h₁,h₂,hD⟩
        rcases (Nat.dvd_prime hp).mp hD with h | h <;> omega
      simp [possiblePrimesInBlock,hlo,hhi,hNo]
    · have hTail := ih (code/1024) hr
      unfold possiblePrimesInBlock
      split
      · exact List.mem_cons_of_mem _ hTail
      · exact hTail

private def possiblePrimesInBlocks (lo hi q : ℕ) : List ℕ → List ℕ
  | [] => []
  | code :: codes =>
    possiblePrimesInBlock lo hi q code wheelResidues ++ possiblePrimesInBlocks lo hi (q+1) codes

private lemma prime_in_wheel_blocks {lo hi n : ℕ} (q : ℕ) (codes : List ℕ)
    (hlo : lo ≤ n) (hhi : n < hi) (hp : n.Prime) (hR : n%210 ∈ wheelResidues)
    (hq : q ≤ n/210) (hqU : n/210 < q+codes.length) :
    n ∈ possiblePrimesInBlocks lo hi q codes := by
  induction codes generalizing q with
  | nil => simp at hqU; omega
  | cons code codes ih =>
    unfold possiblePrimesInBlocks
    rw [List.mem_append]
    by_cases h : n/210 = q
    · have hN : 210*q+n%210 = n := by have := Nat.mod_add_div n 210; omega
      have hp' : (210*q+n%210).Prime := by rwa [hN]
      have hMem := prime_in_wheel_block (lo := lo) (hi := hi) wheelResidues code hR (by omega) (by omega) hp'
      left
      simpa only [hN] using hMem
    · right
      apply ih (q+1) (by omega)
      simp only [List.length_cons] at hqU
      omega

private def witnessCount (lo hi : ℕ) (codes : List ℕ) : ℕ :=
  (possiblePrimesInBlocks lo hi (lo/210) codes).length

private lemma prime_interval_le_witness_count {lo hi : ℕ} (codes : List ℕ) (hl : 8 ≤ lo)
    (hCover : hi/210 < lo/210 + codes.length) :
    ((Ico lo hi).filter Nat.Prime).card ≤ witnessCount lo hi codes := by
  let L := possiblePrimesInBlocks lo hi (lo/210) codes
  apply (card_le_card (t := L.toFinset) ?_).trans (List.toFinset_card_le L)
  intro n hn
  obtain ⟨hnI,hp⟩ := mem_filter.mp hn
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp hnI
  have hCop : n.Coprime 210 := by
    rcases prime_is_fermat_candidate hp with h | h | h | h | h <;> try omega
    exact h.2.1
  have hR : n%210 ∈ wheelResidues := by
    rw [wheel_residues_exact,List.mem_filter,List.mem_range,decide_eq_true_eq]
    refine ⟨Nat.mod_lt _ (by decide),?_⟩
    apply (Nat.add_coprime_iff_left (c := 210) (by exact dvd_mul_right 210 (n/210))).mp
    rwa [Nat.mod_add_div]
  have hq := Nat.div_le_div_right (c := 210) hlo
  have hqU := Nat.div_le_div_right (c := 210) hhi.le
  exact List.mem_toFinset.mpr (prime_in_wheel_blocks (lo/210) codes hlo hhi hp hR hq (by omega))

lemma prime_prefix_add {a b : ℕ} (hab : a ≤ b) :
    b.primesBelow.card = a.primesBelow.card + ((Ico a b).filter Nat.Prime).card := by
  have hEq : b.primesBelow = a.primesBelow ∪ (Ico a b).filter Nat.Prime := by
    ext n
    simp only [Nat.mem_primesBelow,mem_filter,mem_union,mem_Ico]
    grind
  have hDis : Disjoint a.primesBelow ((Ico a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [Nat.mem_primesBelow,mem_filter,mem_Ico] at h₁ h₂
    omega
  rw [hEq, Finset.card_union_of_disjoint hDis]

structure RankInterval where
  upper : ℕ
  budget : ℕ
  increment : ℕ
  divisors : List ℕ

def RankIntervals (ts : List ℕ) (start stop available : ℕ) (rows : List RankInterval) : Prop :=
  match rows with
  | [] => stop < start
  | row :: rest =>
      start ≤ row.upper ∧ (row.upper-1)^64 ≤ 2^row.budget ∧
      (row.upper-1-(start-available))*row.budget < gainedExponent ts (start-available) ∧
      (row.upper+1)/210 < start/210 + row.divisors.length ∧
      witnessCount start (row.upper+1) row.divisors ≤ row.increment ∧
      RankIntervals ts (row.upper+1) stop (available+row.increment) rest

instance (ts : List ℕ) (start stop available : ℕ) (rows : List RankInterval) :
    Decidable (RankIntervals ts start stop available rows) := by
  induction rows generalizing start available with
  | nil => unfold RankIntervals; infer_instance
  | cons row rest ih =>
    unfold RankIntervals
    letI := ih (row.upper+1) (available+row.increment)
    infer_instance

lemma rank_intervals_bound (ts : List ℕ) (start stop available k : ℕ) (rows : List RankInterval)
    (hT : RankThresholds ts 0) (hStart : 8 ≤ start) (hk : start ≤ k) (hStop : k ≤ stop)
    (hP : start.primesBelow.card ≤ available)
    (hRows : RankIntervals ts start stop available rows) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  induction rows generalizing start available with
  | nil => exact (not_lt_of_ge (hk.trans hStop) hRows).elim
  | cons row rows ih =>
    obtain ⟨hUpper,hBudget,hGain,hCover,hInc,hNext⟩ := hRows
    by_cases hK : k ≤ row.upper
    · exact rank_product_on_interval ts start row.upper available row.budget k hT (by omega) hk hK
        hP hBudget hGain
    · apply ih (row.upper+1) (available+row.increment) (by omega) (by omega) _ hNext
      rw [prime_prefix_add (by omega : start ≤ row.upper+1)]
      exact Nat.add_le_add hP ((prime_interval_le_witness_count _ hStart hCover).trans hInc)

def countFromIntervals (n start available : ℕ) : List RankInterval → ℕ
  | [] => available
  | row :: rows =>
      if n ≤ start then available else
        countFromIntervals n (row.upper+1) (available+row.increment) rows

lemma count_from_intervals_valid (ts : List ℕ) (start stop available n : ℕ) (rows : List RankInterval)
    (hStart : 8 ≤ start) (hn : n ≤ stop+1) (hP : start.primesBelow.card ≤ available)
    (hRows : RankIntervals ts start stop available rows) :
    n.primesBelow.card ≤ countFromIntervals n start available rows := by
  have hMono : Monotone (fun t => t.primesBelow.card) := fun a b hab =>
    card_le_card (Nat.primesBelow_mono hab)
  induction rows generalizing start available with
  | nil =>
    have hEnd : stop < start := hRows
    exact (hMono (by omega : n ≤ start)).trans hP
  | cons row rs ih =>
    obtain ⟨hUpper,_,_,hCover,hInc,hNext⟩ := hRows
    by_cases h : n ≤ start
    · exact (hMono h).trans (by simpa only [countFromIntervals, if_pos h] using hP)
    · rw [countFromIntervals, if_neg h]
      apply ih (row.upper+1) (available+row.increment) (by omega) _ hNext
      rw [prime_prefix_add (by omega : start ≤ row.upper+1)]
      exact Nat.add_le_add hP ((prime_interval_le_witness_count _ hStart hCover).trans hInc)

lemma primes_le_candidates (n : ℕ) : n.primesLE.card ≤ (candidatePrefix (n+1)).card := by
  apply card_le_card
  intro p hp
  obtain ⟨hU,hPrime⟩ := Nat.mem_primesLE.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), prime_is_fermat_candidate hPrime⟩

lemma wheel_prime_count_upper (n : ℕ) : n.primesLE.card ≤ 211+48*((n+1)/210+1) := by
  have hBase : (211:ℕ).primeCounting' ≤ 211 := by
    rw [← Nat.primesBelow_card_eq_primeCounting',Nat.primesBelow_eq_filter_range]
    exact (card_filter_le (s := range 211) Nat.Prime).trans_eq (card_range _)
  by_cases h : 211 ≤ n+1
  · have hAdd := Nat.primeCounting'_add_le (a := 210) (k := 211) (by decide) (by decide) (n+1-211)
    have hTotient : Nat.totient 210 = 48 := by decide
    rw [show 211+(n+1-211) = n+1 by omega,hTotient] at hAdd
    rw [Nat.primesLE,Nat.primesBelow_card_eq_primeCounting']
    have hQ := Nat.div_le_div_right (c := 210) (show n+1-211 ≤ n+1 by omega)
    omega
  · have hMono := Nat.monotone_primeCounting' (show n+1 ≤ 211 by omega)
    rw [Nat.primesLE,Nat.primesBelow_card_eq_primeCounting']
    omega

structure NumericRankInterval where
  upper : ℕ
  budget : ℕ
  exponent : ℕ

def NumericRankIntervals (ts : List ℕ) (estimate : ℕ → ℕ → ℕ) (start stop : ℕ) :
    List NumericRankInterval → Prop
  | [] => stop < start
  | row :: rest =>
      start ≤ row.upper ∧ (row.upper-1)^64 ≤ 2^row.budget ∧
      64 < row.exponent ∧ 2^row.exponent ≤ start^64 ∧
      (row.upper-1-(start-estimate start row.exponent))*row.budget <
        gainedExponent ts (start-estimate start row.exponent) ∧
      NumericRankIntervals ts estimate (row.upper+1) stop rest

instance (ts : List ℕ) (estimate : ℕ → ℕ → ℕ) (start stop : ℕ) (rows : List NumericRankInterval) :
    Decidable (NumericRankIntervals ts estimate start stop rows) := by
  induction rows generalizing start with
  | nil => unfold NumericRankIntervals; infer_instance
  | cons row rest ih =>
    unfold NumericRankIntervals
    letI := ih (row.upper+1)
    infer_instance

lemma numeric_rank_intervals_bound (ts : List ℕ) (estimate : ℕ → ℕ → ℕ) (start stop k : ℕ)
    (rows : List NumericRankInterval) (hT : RankThresholds ts 0) (hStart : 3 ≤ start)
    (hk : start ≤ k) (hStop : k ≤ stop)
    (hEstimate : ∀ n f, 64 < f → 2^f ≤ n^64 → ((range n).filter Nat.Prime).card ≤ estimate n f)
    (hRows : NumericRankIntervals ts estimate start stop rows) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  induction rows generalizing start with
  | nil => exact (not_lt_of_ge (hk.trans hStop) hRows).elim
  | cons row rows ih =>
    obtain ⟨hUpper,hBudget,hExp,hPow,hGain,hNext⟩ := hRows
    by_cases h : k ≤ row.upper
    · exact rank_product_on_interval ts start row.upper (estimate start row.exponent) row.budget k hT hStart hk h
        (hEstimate _ _ hExp hPow) hBudget hGain
    · exact ih (row.upper+1) (by omega) (by omega) hNext

private def dyadicRankThresholds : List ℕ := [
  425, 426, 428, 430, 432, 434, 436, 438, 440, 442, 445, 447, 449, 452, 454,
  456, 459, 461, 464, 467, 469, 472, 475, 478, 481, 484, 487, 490, 494, 497,
  500, 504, 508, 511, 515, 519, 523, 527, 531, 536, 540, 545, 550, 554, 559,
  565, 570, 575, 581, 587, 593, 599, 605, 612, 619, 626, 633, 641, 648, 656,
  665, 674, 683, 692, 702, 712, 722, 733, 745, 757, 769, 782, 796, 810, 825,
  840, 857, 874, 892, 912, 932, 953, 976, 1000, 1025, 1053, 1082, 1113, 1146, 1181,
  1220, 1261, 1306, 1354, 1407, 1465, 1528, 1598, 1676, 1763, 1860, 1970, 2094, 2238, 2404,
  2600, 2833, 3115, 3463, 3905, 4483, 5273, 6414, 7172, 7482, 7824, 8203, 8626, 9099, 9634,
  10243, 10941, 11752, 12703, 13835, 15205, 16895, 19035, 21830, 25635, 31118, 39702, 55056, 90393, 257409
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
private def dyadicRankIntervals : List RankInterval := [
  ⟨30041, 952, 3, [
    32786241175626470551833794375024242832435724490974053231309029216974294187356463527190694518581593841917567082984581238486399344352375626763,
    33591459280625328834302805408030447242831511430978740679517773270160168914652383084859945711615961267986943141897980008142688733128631904119867]⟩,
  ⟨30081, 953, 3, [
    33591459280625328834302805408030447242831511430978740679517773270160168914652383084859945711615961267986943141897980008142688733128631904119867]⟩,
  ⟨30123, 953, 7, [
    33591459280625328834302805408030447242831511430978740679517773270160168914652383084859945711615961267986943141897980008142688733128631904119867]⟩,
  ⟨30162, 953, 4, [
    33591459280625328834302805408030447242831511430978740679517773270160168914652383084859945711615961267986943141897980008142688733128631904119867]⟩,
  ⟨30202, 953, 4, [
    33591459280625328834302805408030447242831511430978740679517773270160168914652383084859945711615961267986943141897980008142688733128631904119867]⟩,
  ⟨30243, 953, 4, [
    33591459280625328834302805408030447242831511430978740679517773270160168914652383084859945711615961267986943141897980008142688733128631904119867,
    181637034111251206816161542808949631202738001887401745195822250734080274912824927346511345928358443764818759672154894383546968109778538083328]⟩,
  ⟨30285, 953, 4, [
    181637034111251206816161542808949631202738001887401745195822250734080274912824927346511345928358443764818759672154894383546968109778538083328]⟩,
  ⟨30328, 953, 5, [
    181637034111251206816161542808949631202738001887401745195822250734080274912824927346511345928358443764818759672154894383546968109778538083328]⟩,
  ⟨30372, 953, 3, [
    181637034111251206816161542808949631202738001887401745195822250734080274912824927346511345928358443764818759672154894383546968109778538083328]⟩,
  ⟨30415, 954, 3, [
    181637034111251206816161542808949631202738001887401745195822250734080274912824927346511345928358443764818759672154894383546968109778538083328]⟩,
  ⟨30460, 954, 3, [
    181637034111251206816161542808949631202738001887401745195822250734080274912824927346511345928358443764818759672154894383546968109778538083328,
    70117454319142197931976596727398461056494429089821295068627728492818148021989608994926279161381269215930136952006893382902334716003295668816933]⟩,
  ⟨30508, 954, 5, [
    70117454319142197931976596727398461056494429089821295068627728492818148021989608994926279161381269215930136952006893382902334716003295668816933]⟩,
  ⟨30557, 954, 6, [
    70117454319142197931976596727398461056494429089821295068627728492818148021989608994926279161381269215930136952006893382902334716003295668816933]⟩,
  ⟨30606, 954, 3, [
    70117454319142197931976596727398461056494429089821295068627728492818148021989608994926279161381269215930136952006893382902334716003295668816933]⟩,
  ⟨30658, 954, 4, [
    70117454319142197931976596727398461056494429089821295068627728492818148021989608994926279161381269215930136952006893382902334716003295668816933]⟩,
  ⟨30709, 955, 7, [
    70117454319142197931976596727398461056494429089821295068627728492818148021989608994926279161381269215930136952006893382902334716003295668816933,
    171533939228900918247349051279150315823450465862217418158703545191582472386053166864566124407543114430210690837972058173500807674166509568]⟩,
  ⟨30759, 955, 3, [
    171533939228900918247349051279150315823450465862217418158703545191582472386053166864566124407543114430210690837972058173500807674166509568]⟩,
  ⟨30812, 955, 5, [
    171533939228900918247349051279150315823450465862217418158703545191582472386053166864566124407543114430210690837972058173500807674166509568]⟩,
  ⟨30867, 955, 7, [
    171533939228900918247349051279150315823450465862217418158703545191582472386053166864566124407543114430210690837972058173500807674166509568]⟩,
  ⟨30921, 955, 6, [
    171533939228900918247349051279150315823450465862217418158703545191582472386053166864566124407543114430210690837972058173500807674166509568,
    136645926970376938012485148334540445014025233256290727090814161855662760880994964017504016050021934336644832097864604074803183064366186496]⟩,
  ⟨30976, 955, 5, [
    136645926970376938012485148334540445014025233256290727090814161855662760880994964017504016050021934336644832097864604074803183064366186496]⟩,
  ⟨31033, 955, 5, [
    136645926970376938012485148334540445014025233256290727090814161855662760880994964017504016050021934336644832097864604074803183064366186496]⟩,
  ⟨31088, 956, 6, [
    136645926970376938012485148334540445014025233256290727090814161855662760880994964017504016050021934336644832097864604074803183064366186496,
    204347323205840908480538476146277333395516965371783548573814701522675507584839836384872948549422275204049764552257242683694135672208775432896512]⟩,
  ⟨31144, 956, 4, [
    204347323205840908480538476146277333395516965371783548573814701522675507584839836384872948549422275204049764552257242683694135672208775432896512]⟩,
  ⟨31203, 956, 9, [
    204347323205840908480538476146277333395516965371783548573814701522675507584839836384872948549422275204049764552257242683694135672208775432896512]⟩,
  ⟨31260, 956, 8, [
    204347323205840908480538476146277333395516965371783548573814701522675507584839836384872948549422275204049764552257242683694135672208775432896512]⟩,
  ⟨31315, 956, 4, [
    204347323205840908480538476146277333395516965371783548573814701522675507584839836384872948549422275204049764552257242683694135672208775432896512,
    39631640315791191918696835141658108821299719872911219944199292786614448572223014718222651745838719658815046544641206528349536801268892716614669]⟩,
  ⟨31373, 956, 6, [
    39631640315791191918696835141658108821299719872911219944199292786614448572223014718222651745838719658815046544641206528349536801268892716614669]⟩,
  ⟨31429, 957, 6, [
    39631640315791191918696835141658108821299719872911219944199292786614448572223014718222651745838719658815046544641206528349536801268892716614669]⟩,
  ⟨31485, 957, 3, [
    39631640315791191918696835141658108821299719872911219944199292786614448572223014718222651745838719658815046544641206528349536801268892716614669]⟩,
  ⟨31546, 957, 7, [
    39631640315791191918696835141658108821299719872911219944199292786614448572223014718222651745838719658815046544641206528349536801268892716614669,
    112797639470444845177549748461583317578406326284087639947826825130335100932648187985334929629906661367980225630347546828849281761264371687751697]⟩,
  ⟨31607, 957, 6, [
    112797639470444845177549748461583317578406326284087639947826825130335100932648187985334929629906661367980225630347546828849281761264371687751697]⟩,
  ⟨31670, 957, 8, [
    112797639470444845177549748461583317578406326284087639947826825130335100932648187985334929629906661367980225630347546828849281761264371687751697]⟩,
  ⟨31728, 958, 5, [
    112797639470444845177549748461583317578406326284087639947826825130335100932648187985334929629906661367980225630347546828849281761264371687751697,
    179916982958705033024275325480042780315437677541733378245156707068979831595371033581255705789735813349697628668974572494269741156268463750119443]⟩,
  ⟨31789, 958, 5, [
    179916982958705033024275325480042780315437677541733378245156707068979831595371033581255705789735813349697628668974572494269741156268463750119443]⟩,
  ⟨31852, 958, 5, [
    179916982958705033024275325480042780315437677541733378245156707068979831595371033581255705789735813349697628668974572494269741156268463750119443]⟩,
  ⟨31918, 958, 5, [
    179916982958705033024275325480042780315437677541733378245156707068979831595371033581255705789735813349697628668974572494269741156268463750119443]⟩,
  ⟨31987, 958, 4, [
    179916982958705033024275325480042780315437677541733378245156707068979831595371033581255705789735813349697628668974572494269741156268463750119443,
    57923068853410104070857830826977313577816102271450132523134597874836256092220947215140703528030880504518628102384973659721831226421156712060041]⟩,
  ⟨32061, 958, 8, [
    57923068853410104070857830826977313577816102271450132523134597874836256092220947215140703528030880504518628102384973659721831226421156712060041]⟩,
  ⟨32132, 959, 8, [
    57923068853410104070857830826977313577816102271450132523134597874836256092220947215140703528030880504518628102384973659721831226421156712060041,
    222579275958323074036080641538349197442011754333679696733712934924352018216833736887311902280826935622873170495357082296435109167532479225004043]⟩,
  ⟨32204, 959, 8, [
    222579275958323074036080641538349197442011754333679696733712934924352018216833736887311902280826935622873170495357082296435109167532479225004043]⟩,
  ⟨32277, 959, 6, [
    222579275958323074036080641538349197442011754333679696733712934924352018216833736887311902280826935622873170495357082296435109167532479225004043]⟩,
  ⟨32353, 959, 9, [
    222579275958323074036080641538349197442011754333679696733712934924352018216833736887311902280826935622873170495357082296435109167532479225004043,
    33573110963738895103322090152698710171409989599452332793387558359059474145645790422935340590952657153137263618009996658080758113530267907927040]⟩,
  ⟨32425, 960, 10, [
    33573110963738895103322090152698710171409989599452332793387558359059474145645790422935340590952657153137263618009996658080758113530267907927040]⟩,
  ⟨32495, 960, 6, [
    33573110963738895103322090152698710171409989599452332793387558359059474145645790422935340590952657153137263618009996658080758113530267907927040]⟩,
  ⟨32568, 960, 8, [
    33573110963738895103322090152698710171409989599452332793387558359059474145645790422935340590952657153137263618009996658080758113530267907927040,
    51825936037311953889268721032204620957872555114003179486361483051050434468487956788691774888939793276234782257688986953611872251624519448395819]⟩,
  ⟨32642, 960, 9, [
    51825936037311953889268721032204620957872555114003179486361483051050434468487956788691774888939793276234782257688986953611872251624519448395819]⟩,
  ⟨32716, 960, 6, [
    51825936037311953889268721032204620957872555114003179486361483051050434468487956788691774888939793276234782257688986953611872251624519448395819]⟩,
  ⟨32789, 961, 7, [
    51825936037311953889268721032204620957872555114003179486361483051050434468487956788691774888939793276234782257688986953611872251624519448395819,
    68474110784326149934709013493831914043465478937895162087407076601913449236611658174705299626918032886948046955713062639772855951449289392309]⟩,
  ⟨32864, 961, 7, [
    68474110784326149934709013493831914043465478937895162087407076601913449236611658174705299626918032886948046955713062639772855951449289392309]⟩,
  ⟨32941, 961, 8, [
    68474110784326149934709013493831914043465478937895162087407076601913449236611658174705299626918032886948046955713062639772855951449289392309]⟩,
  ⟨33020, 961, 8, [
    68474110784326149934709013493831914043465478937895162087407076601913449236611658174705299626918032886948046955713062639772855951449289392309,
    122111849946530353828783528049872084721881525819783683453110836792330382581061815362387603045862547027162185947719709837209662145488257823744]⟩,
  ⟨33100, 961, 9, [
    122111849946530353828783528049872084721881525819783683453110836792330382581061815362387603045862547027162185947719709837209662145488257823744]⟩,
  ⟨33177, 962, 6, [
    122111849946530353828783528049872084721881525819783683453110836792330382581061815362387603045862547027162185947719709837209662145488257823744]⟩,
  ⟨33258, 962, 8, [
    122111849946530353828783528049872084721881525819783683453110836792330382581061815362387603045862547027162185947719709837209662145488257823744,
    527491121255922137351008744724808821531807840410176278509804215782202846846987540725121039405232529697235479132068490741342419601410302315331584]⟩,
  ⟨33340, 962, 7, [
    527491121255922137351008744724808821531807840410176278509804215782202846846987540725121039405232529697235479132068490741342419601410302315331584]⟩,
  ⟨33426, 962, 10, [
    527491121255922137351008744724808821531807840410176278509804215782202846846987540725121039405232529697235479132068490741342419601410302315331584,
    31231351590586067303962409458003105810027510224581900690431512115997105734166946009372488189885756740133891363390483761894843308178432]⟩,
  ⟨33508, 963, 8, [
    31231351590586067303962409458003105810027510224581900690431512115997105734166946009372488189885756740133891363390483761894843308178432]⟩,
  ⟨33592, 963, 10, [
    31231351590586067303962409458003105810027510224581900690431512115997105734166946009372488189885756740133891363390483761894843308178432]⟩,
  ⟨33676, 963, 10, [
    31231351590586067303962409458003105810027510224581900690431512115997105734166946009372488189885756740133891363390483761894843308178432,
    217330726717263092814536792794751728050165173730363856849719096962816201078479891091309957581627570607836597823701013622938945914232327130112]⟩,
  ⟨33760, 963, 8, [
    217330726717263092814536792794751728050165173730363856849719096962816201078479891091309957581627570607836597823701013622938945914232327130112]⟩,
  ⟨33846, 963, 9, [
    217330726717263092814536792794751728050165173730363856849719096962816201078479891091309957581627570607836597823701013622938945914232327130112,
    211466563527972656567351401508156750446956411394457419607841248814617309580085236642665283362112630136056077513788710799622196654778249935872]⟩,
  ⟨33930, 964, 8, [
    211466563527972656567351401508156750446956411394457419607841248814617309580085236642665283362112630136056077513788710799622196654778249935872]⟩,
  ⟨34016, 964, 6, [
    211466563527972656567351401508156750446956411394457419607841248814617309580085236642665283362112630136056077513788710799622196654778249935872]⟩,
  ⟨34107, 964, 6, [
    211466563527972656567351401508156750446956411394457419607841248814617309580085236642665283362112630136056077513788710799622196654778249935872,
    39688138889563290403592031672979224458775503655160266934308019327952618093756085367994582020688748277898692338741533722115215098823926043639821]⟩,
  ⟨34203, 964, 9, [
    39688138889563290403592031672979224458775503655160266934308019327952618093756085367994582020688748277898692338741533722115215098823926043639821]⟩,
  ⟨34298, 965, 11, [
    39688138889563290403592031672979224458775503655160266934308019327952618093756085367994582020688748277898692338741533722115215098823926043639821,
    503054734755707030468364885888503445348890478851773192451153584733160955148940041183749625560547303434096045881366558887206555756264522752]⟩,
  ⟨34393, 965, 11, [
    503054734755707030468364885888503445348890478851773192451153584733160955148940041183749625560547303434096045881366558887206555756264522752]⟩,
  ⟨34489, 965, 9, [
    503054734755707030468364885888503445348890478851773192451153584733160955148940041183749625560547303434096045881366558887206555756264522752,
    32803852818605743799610017255949918846695201445918778279236132099778020766883511158499168950304277908294884137015000852781472866465790082059]⟩,
  ⟨34587, 965, 9, [
    32803852818605743799610017255949918846695201445918778279236132099778020766883511158499168950304277908294884137015000852781472866465790082059]⟩,
  ⟨34685, 966, 11, [
    32803852818605743799610017255949918846695201445918778279236132099778020766883511158499168950304277908294884137015000852781472866465790082059,
    33534408255347602743955017544388353149049549350070554587745487227214267832329971160937687185304842482701308160033434644574463400488514115087360]⟩,
  ⟨34783, 966, 11, [
    33534408255347602743955017544388353149049549350070554587745487227214267832329971160937687185304842482701308160033434644574463400488514115087360]⟩,
  ⟨34882, 966, 8, [
    33534408255347602743955017544388353149049549350070554587745487227214267832329971160937687185304842482701308160033434644574463400488514115087360,
    31980904142660171925410453181342004049064739153427500837786299947251322601247196645228376798622490273252206896121234652296738051797811271]⟩,
  ⟨34981, 967, 9, [
    31980904142660171925410453181342004049064739153427500837786299947251322601247196645228376798622490273252206896121234652296738051797811271]⟩,
  ⟨35083, 967, 8, [
    31980904142660171925410453181342004049064739153427500837786299947251322601247196645228376798622490273252206896121234652296738051797811271,
    38703216713145508220161388373332391654466211848160335298557718658114803247636182775299255660459741343518461553129785323423833558731271962641]⟩,
  ⟨35190, 967, 11, [
    38703216713145508220161388373332391654466211848160335298557718658114803247636182775299255660459741343518461553129785323423833558731271962641]⟩,
  ⟨35299, 967, 9, [
    38703216713145508220161388373332391654466211848160335298557718658114803247636182775299255660459741343518461553129785323423833558731271962641,
    70168048163191102827783328653359756905047403211620411871725196912374790003157079974790726754592880088594829377737874589473679283980053781676032]⟩,
  ⟨35409, 968, 12, [
    70168048163191102827783328653359756905047403211620411871725196912374790003157079974790726754592880088594829377737874589473679283980053781676032]⟩,
  ⟨35520, 968, 9, [
    70168048163191102827783328653359756905047403211620411871725196912374790003157079974790726754592880088594829377737874589473679283980053781676032,
    88674228469705020422817749576609673515274178249023671102812887769032095715644340993830947782713954435141766666464346991263076592024574707764224]⟩,
  ⟨35636, 968, 13, [
    88674228469705020422817749576609673515274178249023671102812887769032095715644340993830947782713954435141766666464346991263076592024574707764224]⟩,
  ⟨35749, 969, 5, [
    88674228469705020422817749576609673515274178249023671102812887769032095715644340993830947782713954435141766666464346991263076592024574707764224,
    454238802762810291684888377040164613395209673988761459468365190594628255883347289474974498215402881570247469753760477699624922734585575508030483]⟩,
  ⟨35871, 969, 13, [
    454238802762810291684888377040164613395209673988761459468365190594628255883347289474974498215402881570247469753760477699624922734585575508030483]⟩,
  ⟨35995, 969, 12, [
    454238802762810291684888377040164613395209673988761459468365190594628255883347289474974498215402881570247469753760477699624922734585575508030483,
    57923069029025194416810621950199443454392089970393704441519568392081706220593012559344328315642136299513830744644582845114817700371340638307328]⟩,
  ⟨36122, 969, 13, [
    57923069029025194416810621950199443454392089970393704441519568392081706220593012559344328315642136299513830744644582845114817700371340638307328,
    51825970536548474423236247418878579707600642757750920389185145599716715474687429171329754737568509688599568843919078661744142291508368239493161]⟩,
  ⟨36247, 970, 10, [
    51825970536548474423236247418878579707600642757750920389185145599716715474687429171329754737568509688599568843919078661744142291508368239493161]⟩,
  ⟨36378, 970, 13, [
    51825970536548474423236247418878579707600642757750920389185145599716715474687429171329754737568509688599568843919078661744142291508368239493161,
    185963536688909253759546741376990782188272941243885682747443632041221257270274196783755307593126496061297177472337527296431205558200629681193007]⟩,
  ⟨36512, 970, 11, [
    185963536688909253759546741376990782188272941243885682747443632041221257270274196783755307593126496061297177472337527296431205558200629681193007]⟩,
  ⟨36647, 971, 15, [
    185963536688909253759546741376990782188272941243885682747443632041221257270274196783755307593126496061297177472337527296431205558200629681193007,
    49734571375529430426835927320557636185227979835744121899466314158322420007239480625268480409869510575153891485738115259047213961214689280]⟩,
  ⟨36784, 971, 15, [
    49734571375529430426835927320557636185227979835744121899466314158322420007239480625268480409869510575153891485738115259047213961214689280,
    39664321838292609804287998856410521066624573018027544161822945071505752152119078608804598887227974267038749083322831339247031553480139641716747]⟩,
  ⟨36918, 972, 14, [
    39664321838292609804287998856410521066624573018027544161822945071505752152119078608804598887227974267038749083322831339247031553480139641716747]⟩,
  ⟨37054, 972, 15, [
    39664321838292609804287998856410521066624573018027544161822945071505752152119078608804598887227974267038749083322831339247031553480139641716747,
    33534620643002375533823944491969829469820798568198379653759974786105335951452773353271654219729151557921906614436757049187206254871573832936471]⟩,
  ⟨37191, 972, 11, [
    33534620643002375533823944491969829469820798568198379653759974786105335951452773353271654219729151557921906614436757049187206254871573832936471,
    31980903869115150202125201967291288778297706614498739109835938042144813956686009789645866004213225619482410900884387430649830379248156672]⟩,
  ⟨37330, 973, 12, [
    31980903869115150202125201967291288778297706614498739109835938042144813956686009789645866004213225619482410900884387430649830379248156672]⟩,
  ⟨37474, 973, 13, [
    31980903869115150202125201967291288778297706614498739109835938042144813956686009789645866004213225619482410900884387430649830379248156672,
    154089809550668720231073226038665714279601719407541672907938076518152173885673475962519365290103401541058889607170421801610394115926797341]⟩,
  ⟨37623, 973, 20, [
    154089809550668720231073226038665714279601719407541672907938076518152173885673475962519365290103401541058889607170421801610394115926797341,
    68558335830559292092561778288292426417280086631819307979250685409623027158219779772926197310289172989839852039379609327070062835722204761088]⟩,
  ⟨37765, 974, 10, [
    68558335830559292092561778288292426417280086631819307979250685409623027158219779772926197310289172989839852039379609327070062835722204761088]⟩,
  ⟨37915, 974, 14, [
    68558335830559292092561778288292426417280086631819307979250685409623027158219779772926197310289172989839852039379609327070062835722204761088,
    582317973323971874746960053182170320496326444499804196238387379692516467896657146424309698831518598701139026054439160080387021129751047524319335]⟩,
  ⟨38069, 974, 13, [
    582317973323971874746960053182170320496326444499804196238387379692516467896657146424309698831518598701139026054439160080387021129751047524319335,
    56603323724596595389799303066121087623353234788271569871689836145533075011176183772856931846281928562305005828599876260705579930527164728320]⟩,
  ⟨38225, 975, 12, [
    56603323724596595389799303066121087623353234788271569871689836145533075011176183772856931846281928562305005828599876260705579930527164728320,
    253339117240700441252533621537004057818329402033081187892380904972589717579618344364477363140694731358583095772405275922844018200906689997176869]⟩,
  ⟨38388, 975, 17, [
    253339117240700441252533621537004057818329402033081187892380904972589717579618344364477363140694731358583095772405275922844018200906689997176869]⟩,
  ⟨38549, 975, 9, [
    253339117240700441252533621537004057818329402033081187892380904972589717579618344364477363140694731358583095772405275922844018200906689997176869,
    55276683387077656005941632764892489986851942506470366013570704467931808400003810062532450124158886548172371656744847977917205527997199360]⟩,
  ⟨38722, 976, 20, [
    55276683387077656005941632764892489986851942506470366013570704467931808400003810062532450124158886548172371656744847977917205527997199360,
    161575082561635797336809485268588760024051894966229331609589528965098860967747105564638833041027418822315927518513366214374770169019985463083025]⟩,
  ⟨38895, 976, 17, [
    161575082561635797336809485268588760024051894966229331609589528965098860967747105564638833041027418822315927518513366214374770169019985463083025,
    423803588278897032372224645586806388879224519155156738273489447095813907842636612297216946372835798742893923000292712344188243012923737104187392]⟩,
  ⟨39068, 977, 15, [
    423803588278897032372224645586806388879224519155156738273489447095813907842636612297216946372835798742893923000292712344188243012923737104187392,
    326231190913431572339113004637138463566435531008464728008799242481630132390448615524643358882113294426198600432182670791103969785337001035260939]⟩,
  ⟨39247, 977, 22, [
    326231190913431572339113004637138463566435531008464728008799242481630132390448615524643358882113294426198600432182670791103969785337001035260939]⟩,
  ⟨39420, 978, 16, [
    326231190913431572339113004637138463566435531008464728008799242481630132390448615524643358882113294426198600432182670791103969785337001035260939,
    33620922468968121648631081865237389552804962109718207070715510080572979945320285631824374938449121330522251504842085802695702816398026411617453]⟩,
  ⟨39598, 978, 14, [
    33620922468968121648631081865237389552804962109718207070715510080572979945320285631824374938449121330522251504842085802695702816398026411617453,
    39631605648991099554249019990827323669989605434578789143193907872001060324136472066501103298183756270505275988997391405021098340400644356064269]⟩,
  ⟨39784, 978, 17, [
    39631605648991099554249019990827323669989605434578789143193907872001060324136472066501103298183756270505275988997391405021098340400644356064269,
    52162319517270793595436227102136786376779764667529061406234513999625019472814908592326377942354515279193512181765888965991503045035447191368723]⟩,
  ⟨39972, 979, 19, [
    52162319517270793595436227102136786376779764667529061406234513999625019472814908592326377942354515279193512181765888965991503045035447191368723,
    57923362447666193400543644503424456868919311715026044272764622398361944379170498375555067799026681363347685756209281558588052361550542878649344]⟩,
  ⟨40163, 979, 19, [
    57923362447666193400543644503424456868919311715026044272764622398361944379170498375555067799026681363347685756209281558588052361550542878649344,
    70632492356079524484991161804459513454364234920672357817252747088499321732779560179260302901602445610963147467710345428724312804285579056436224]⟩,
  ⟨40354, 980, 14, [
    70632492356079524484991161804459513454364234920672357817252747088499321732779560179260302901602445610963147467710345428724312804285579056436224,
    90159280299741697951985106584897662116243252709829109813073259675548484534702568340209872570529240336276257524402985191257431815689894973]⟩,
  ⟨40554, 980, 18, [
    90159280299741697951985106584897662116243252709829109813073259675548484534702568340209872570529240336276257524402985191257431815689894973,
    39107378809534093577403726869688687186930484939876043438640090073184865964947083185968768001986565504936956123192106414545819506794536442880]⟩,
  ⟨40756, 981, 15, [
    39107378809534093577403726869688687186930484939876043438640090073184865964947083185968768001986565504936956123192106414545819506794536442880,
    37795644163137515751994394217237191913153693163979393279135845807811856969068015180271574882440900145935993105039069949476364880796713091]⟩,
  ⟨40968, 981, 23, [
    37795644163137515751994394217237191913153693163979393279135845807811856969068015180271574882440900145935993105039069949476364880796713091,
    240838089793931651047333763831323482612497198858677175101563480568100761308363708207807263768005890089490851019468074412823163278044888250187807]⟩,
  ⟨41178, 982, 19, [
    240838089793931651047333763831323482612497198858677175101563480568100761308363708207807263768005890089490851019468074412823163278044888250187807,
    125167536105764828643257175386387439429239947634974193717572141128248305901442587829544083474971149537452667030453325533359654522383597271266304]⟩,
  ⟨41394, 982, 23, [
    125167536105764828643257175386387439429239947634974193717572141128248305901442587829544083474971149537452667030453325533359654522383597271266304,
    33321447202756372416976998383717545363981775932484324151564642734071067719675857594689330919419737443878430819725886225235377624716013469707]⟩,
  ⟨41608, 983, 19, [
    33321447202756372416976998383717545363981775932484324151564642734071067719675857594689330919419737443878430819725886225235377624716013469707,
    33656470748401818992203064587049214672264822262569944899574955745846606547071321488713120839632437971624881517108681959233069078660384624225323]⟩,
  ⟨41829, 983, 22, [
    33656470748401818992203064587049214672264822262569944899574955745846606547071321488713120839632437971624881517108681959233069078660384624225323,
    592481132432150615766053104692082140254642801156950905822156609608801497839241105311560391049913064146548915734072069733097449774645651701783]⟩,
  ⟨42050, 984, 25, [
    592481132432150615766053104692082140254642801156950905822156609608801497839241105311560391049913064146548915734072069733097449774645651701783,
    56565496965534071168312269870143005451750936121736851595086222051005450391150087576611673801566330841384764982336772385530201078721390095457]⟩,
  ⟨42272, 984, 21, [
    56565496965534071168312269870143005451750936121736851595086222051005450391150087576611673801566330841384764982336772385530201078721390095457,
    39631573392985716121669942887823169452525115740034763229124991858449173630072620497839065566305108303317432946591722700307300221512446801608717]⟩,
  ⟨42495, 984, 28, [
    39631573392985716121669942887823169452525115740034763229124991858449173630072620497839065566305108303317432946591722700307300221512446801608717,
    143334047323273935806568174120681015566751884755085119421088216399676322645767165567699361897558159917433403921010036509089580849964631007059003]⟩,
  ⟨42716, 985, 20, [
    143334047323273935806568174120681015566751884755085119421088216399676322645767165567699361897558159917433403921010036509089580849964631007059003,
    328562334860392102618311903205538015545422380465890161447543056729778071435511703987907861735585749306312402818827260404983545705030221913]⟩,
  ⟨42944, 985, 24, [
    328562334860392102618311903205538015545422380465890161447543056729778071435511703987907861735585749306312402818827260404983545705030221913,
    574586428444508998323759104196064454340214600965961378451533356734275125156775376220707402574530983704267227692760763834185792356175772197888]⟩,
  ⟨43170, 986, 19, [
    574586428444508998323759104196064454340214600965961378451533356734275125156775376220707402574530983704267227692760763834185792356175772197888,
    551975221714822749559138604730741534070035672714645491840480225584227972829981615393831162744612623560660963509252709574410986961720831499060224]⟩,
  ⟨43405, 986, 18, [
    551975221714822749559138604730741534070035672714645491840480225584227972829981615393831162744612623560660963509252709574410986961720831499060224,
    51864606429691756100107737722566365166366033906405799132138914301141420268698633750581979930544250610732050097680968354598531457083610133168128]⟩,
  ⟨43646, 987, 21, [
    51864606429691756100107737722566365166366033906405799132138914301141420268698633750581979930544250610732050097680968354598531457083610133168128,
    94506097557763909922523233031556041247994079559681163483346210521095886982512496850579916136562662201849727571216856672960186392471926075293725]⟩,
  ⟨43895, 987, 21, [
    94506097557763909922523233031556041247994079559681163483346210521095886982512496850579916136562662201849727571216856672960186392471926075293725,
    32798077910400725411261956717087841521486797645463855163186338008997038038852926995949684579788440573014875091795961430729294210710279028747,
    33534408292304516935846868823475760066997889251521026116312679849887593551345323904529092408800461659077736649735765791602260112091485605735424]⟩,
  ⟨44148, 988, 27, [
    33534408292304516935846868823475760066997889251521026116312679849887593551345323904529092408800461659077736649735765791602260112091485605735424,
    179958694606205962752229644387229410549406656694458816780536286261202583897462470258420451859055982209812451730743935993417341807189715690979328]⟩,
  ⟨44399, 989, 23, [
    179958694606205962752229644387229410549406656694458816780536286261202583897462470258420451859055982209812451730743935993417341807189715690979328,
    139925718781425328682783215596068781288401268652258224563841067939657942897030181512352699475082982396892768044127313831577997670492379569225]⟩,
  ⟨44658, 989, 25, [
    139925718781425328682783215596068781288401268652258224563841067939657942897030181512352699475082982396892768044127313831577997670492379569225,
    586777075315918416211302437624192918159145926583654338711094727970190744862258132376316379755673298011711787333755275041660256979903651512531]⟩,
  ⟨44918, 990, 24, [
    586777075315918416211302437624192918159145926583654338711094727970190744862258132376316379755673298011711787333755275041660256979903651512531,
    532906997463056972272251903884938449181302303749520509628312440174428563651593049663445945268870380082850660999145190765720835489824368492585]⟩,
  ⟨45185, 990, 23, [
    532906997463056972272251903884938449181302303749520509628312440174428563651593049663445945268870380082850660999145190765720835489824368492585,
    39631573423914846559539039134794808795878014406661489540795464201689569296900443212757401077436733369780353405245912324734906949298636349062157,
    204556120681260507361580930539910714034431541028809416138547739419947339613763920506331810686420028304543644745050197555905202286078771845922979]⟩,
  ⟨45457, 991, 24, [
    204556120681260507361580930539910714034431541028809416138547739419947339613763920506331810686420028304543644745050197555905202286078771845922979,
    86336811057328919910091218038668874951559951353663559358129652125439131987280576518193283761417992099992476741293121486851294239190200413184]⟩,
  ⟨45738, 991, 24, [
    86336811057328919910091218038668874951559951353663559358129652125439131987280576518193283761417992099992476741293121486851294239190200413184,
    110153862530216685011406334034031598891606184734723124235430501986183261980354663394079835440341039896159830348002358649831102971043361344711]⟩,
  ⟨46024, 992, 24, [
    110153862530216685011406334034031598891606184734723124235430501986183261980354663394079835440341039896159830348002358649831102971043361344711,
    66957178378446711002157238089427682455020065106629321288818343898072053764569244459993593552855683571923752758965745577647730925352547345,
    32748445562028033214529482193486212635774876077130588142008616017427857594905852980009928213822676546742647125681503441051074990441206281227]⟩,
  ⟨46321, 992, 28, [
    32748445562028033214529482193486212635774876077130588142008616017427857594905852980009928213822676546742647125681503441051074990441206281227,
    33534446099291671392409725871388384279887405244852140416966012570856847385205876109925352180783911082336075235267995101496282681038797364276271]⟩,
  ⟨46620, 993, 27, [
    33534446099291671392409725871388384279887405244852140416966012570856847385205876109925352180783911082336075235267995101496282681038797364276271,
    378127752909894613572848229229287513360985891143521474508555055011248829747051689396335166275941192987914070080550113085275037553845488120832,
    36909779013225136793034002254143872054235597587097240682573578164492333690504867601803510910865139829256557872118848595337249382478871]⟩,
  ⟨46923, 994, 31, [
    36909779013225136793034002254143872054235597587097240682573578164492333690504867601803510910865139829256557872118848595337249382478871,
    52215998178234449083199369472298072549980410607339655874210486924017918607744015663780967198921609254540949748291014072073379553648865728035840]⟩,
  ⟨47232, 994, 23, [
    52215998178234449083199369472298072549980410607339655874210486924017918607744015663780967198921609254540949748291014072073379553648865728035840,
    113086337211187380088649136741057480953500640578796355275245350032995385991831039109654094618996115399817428897592557598712793015659873772240896]⟩,
  ⟨47550, 995, 32, [
    113086337211187380088649136741057480953500640578796355275245350032995385991831039109654094618996115399817428897592557598712793015659873772240896,
    68523478803079269809668038753519626666999996792060106251464157105553493268250223623226317148820631253408088353730204026453826196706092555264,
    222546527512808378869235907437898055035171803920402401602006004792689235189025398876401305372321822909973095060583421937325409589287430019650591]⟩,
  ⟨47872, 995, 32, [
    222546527512808378869235907437898055035171803920402401602006004792689235189025398876401305372321822909973095060583421937325409589287430019650591,
    39632012468605385962465091071629163236170832703332445488893184315123484120107288436817271011746956792957486375381051297806572999269893861801997]⟩,
  ⟨48197, 996, 29, [
    39632012468605385962465091071629163236170832703332445488893184315123484120107288436817271011746956792957486375381051297806572999269893861801997,
    57923449668329936777568288843778380347462366741629093207868451070596563688452811731274516226912765942098047332902110837482760604220045392956416,
    128333702994921451142134777420139212616766540580175956635899933427663783998581263363199684125450635105745316853664278792921059573320071093248]⟩,
  ⟨48527, 997, 29, [
    128333702994921451142134777420139212616766540580175956635899933427663783998581263363199684125450635105745316853664278792921059573320071093248,
    545729028438711088564508110935968118383474670130383248386924963751620270352027442601825654625120174027664913674694445091946876975208875929108491,
    33734030470860153709340494875901535400426840963807087524285409352624527122643366856917250998081470969154533856580915388215326080809400080018571]⟩,
  ⟨48868, 997, 33, [
    33734030470860153709340494875901535400426840963807087524285409352624527122643366856917250998081470969154533856580915388215326080809400080018571,
    344528565065346125112323381416161393960738001703299452596253983948929853849331551846389371394768196394562261199315913555508458406944912061759571]⟩,
  ⟨49211, 998, 36, [
    344528565065346125112323381416161393960738001703299452596253983948929853849331551846389371394768196394562261199315913555508458406944912061759571,
    217368388887844373850680504960519076884070883787842476449736158079189881882461387040501199823496494689063889676746425001043567886029070382247,
    185963836146300330565690236822008415237314761488314861586127462245451399735563289144886941745151388114750431537553286847808373759681743574555805]⟩,
  ⟨49554, 999, 32, [
    185963836146300330565690236822008415237314761488314861586127462245451399735563289144886941745151388114750431537553286847808373759681743574555805,
    37206454625407214657354545066778637326171732275135587461940438543516178153132496456474205989128785538060326267583770484038704711087121]⟩,
  ⟨49906, 999, 31, [
    37206454625407214657354545066778637326171732275135587461940438543516178153132496456474205989128785538060326267583770484038704711087121,
    478678074546187450502602057647908968162194270329453440915889322154225302770079417429124876060789258956442657361149570233384245483715710789110813,
    70436036502426558813560884720501336130828281336472757464772960948378164682629479174863234373281129438923015115887411950580026174580760921574471]⟩,
  ⟨50264, 1000, 37, [
    70436036502426558813560884720501336130828281336472757464772960948378164682629479174863234373281129438923015115887411950580026174580760921574471,
    94562625497553915664907635760912584747948785322654604445911204846595437557372856811375810299631850212346761571808031040498400886124640378814615,
    308028901823697516177681225019540217640136532202235865697912451835848324080323217350044450366715089342832990358851588935466970490561122322629685]⟩,
  ⟨50621, 1001, 32, [
    308028901823697516177681225019540217640136532202235865697912451835848324080323217350044450366715089342832990358851588935466970490561122322629685,
    39631628632426541591181168463728759555752029205915615625752818400349083123488832946507518027078947657511739537152660743976813868998603754700813,
    271356664213036434772652373915272210368462842617709496403353161967906568026802619034148797576819386926043456044033408427202951536098934439246859]⟩,
  ⟨50989, 1001, 30, [
    271356664213036434772652373915272210368462842617709496403353161967906568026802619034148797576819386926043456044033408427202951536098934439246859,
    34019730495710489036655640333524633803705330251792324825129539293858961279157005525112490712919858366597494862751674664957052526286625912663040]⟩,
  ⟨51366, 1002, 34, [
    34019730495710489036655640333524633803705330251792324825129539293858961279157005525112490712919858366597494862751674664957052526286625912663040,
    32494848696398208001239926076802376151597534222944250059090614864203660107800503332192501918509865643147657714021655747722358834702887936,
    53945061568814574156682816551664858615988658513542490925832286344473897847691203126238275555923539139085954955583637631336849792357376]⟩,
  ⟨51749, 1003, 40, [
    53945061568814574156682816551664858615988658513542490925832286344473897847691203126238275555923539139085954955583637631336849792357376,
    38702830790796122715268458289743650402687798421284804906914379061076144955200733383521623116375499732629311625768015582581879950629959368727,
    37795666720588274663964417868113333457901687766733364486079963785104227900829462807190760675923874638226288795213340947565182582373125139]⟩,
  ⟨52137, 1003, 35, [
    37795666720588274663964417868113333457901687766733364486079963785104227900829462807190760675923874638226288795213340947565182582373125139,
    57923068836141654446185203623843154568454331825383539618539531637234487986539481907154384772104299216111888566794759648312144607956346189411328,
    68651408559983498167090851362493765422039645485454260297367837660896306702783097389688224821770913907041484668409907023811121204343941903360]⟩,
  ⟨52531, 1004, 33, [
    68651408559983498167090851362493765422039645485454260297367837660896306702783097389688224821770913907041484668409907023811121204343941903360,
    143283593052348058144483436026792977608929449427801190006364873974278926867547047538871483661181544129231361129925707251576216282056093649076224,
    449546908923904128905864755359869524904828048372289475871548604387357854194436422556073254280480792642321782648108863309712733305188840898560]⟩,
  ⟨52933, 1005, 37, [
    449546908923904128905864755359869524904828048372289475871548604387357854194436422556073254280480792642321782648108863309712733305188840898560,
    467964936895622158130760247905047073544919851265756141746977186646120588482126180766531027056841135584677139447326622281249841585305873809408,
    32748446041596997979084342400053988598975767718418603375515326298170077496519216746788482284939876353930794606068094916908196133304267744267]⟩,
  ⟨53346, 1005, 40, [
    32748446041596997979084342400053988598975767718418603375515326298170077496519216746788482284939876353930794606068094916908196133304267744267,
    33585019489594614065203845346633577350480009069446251227590550231795421932156693094822025568209101472781632688134330740423211445947709470551053,
    110185892066712161221427100129179654209889937287507765860735041412026296571686532614063915497236807208590861651906351519401845661993036446761]⟩,
  ⟨53762, 1006, 37, [
    110185892066712161221427100129179654209889937287507765860735041412026296571686532614063915497236807208590861651906351519401845661993036446761,
    175857808979722369855178542141097574605735635177089018528834732054449561044989736707911044938771182539118750468399551822011033541869686508544,
    88409124635199792843144953866617135528811159589560605382233670440926608430597211241365871916099929281855595383311541832092044201945960397423653]⟩,
  ⟨54185, 1007, 39, [
    88409124635199792843144953866617135528811159589560605382233670440926608430597211241365871916099929281855595383311541832092044201945960397423653,
    51882469164348684485594607215247951042942979924780273991965397497627392898978372116853048595113469815344146490819589645026693933686634541243423,
    417694514647133323304160897671055977993890062290468435582620662039112523296624410046617982847200616752668426577235802117083525897667479953521664]⟩,
  ⟨54614, 1008, 41, [
    417694514647133323304160897671055977993890062290468435582620662039112523296624410046617982847200616752668426577235802117083525897667479953521664,
    216684593552801375666784950987969895186064839507582640843172204693418094900020699435688686621606838434114325160785197690757374870608973483999341,
    70117507097281363337100380043396638651449469101077173265729755268601242779532863982852491284241734803600983057941963796699704304281013523153920]⟩,
  ⟨55052, 1008, 38, [
    70117507097281363337100380043396638651449469101077173265729755268601242779532863982852491284241734803600983057941963796699704304281013523153920,
    112797749870402570005061331267165999800586716737008792068193146216286430662945263761515622574258254191338219707129683202765797703020212636365883,
    36044706067714012724458217062876507971018179708300598947405631143534492967367383265368970066688872272323994420022529798038334063616]⟩,
  ⟨55499, 1009, 37, [
    36044706067714012724458217062876507971018179708300598947405631143534492967367383265368970066688872272323994420022529798038334063616,
    32873516203221279882833162981200868459420913534654810775064470034512285888800774175769408873735870912026293495391260866636469924709925950475,
    33534475124510237778416209756030397115521638190379926026751414569412866264975133952279362728999104188136536246088815759843915376147582250134528]⟩,
  ⟨55956, 1010, 48, [
    33534475124510237778416209756030397115521638190379926026751414569412866264975133952279362728999104188136536246088815759843915376147582250134528,
    253032385180397326379925476494321147759809633897965753776570508093950478945281273596094448141082628622780547016092381884732837490297115177386003,
    39813262722336998988666378236336679965311750048573227887395055306485673394161126424398619840872828908226568541937536987244744736676790794190861]⟩,
  ⟨56413, 1011, 38, [
    39813262722336998988666378236336679965311750048573227887395055306485673394161126424398619840872828908226568541937536987244744736676790794190861,
    509113288967901916859323050722177722694674152300121119458046796342642653693131406773760384753273194810926904354979125486783445404292068070653999,
    413128130850898355485492391548810646030952171349358231703620074377114265132370690118327502187128007153215556247827587573200412922903]⟩,
  ⟨56886, 1011, 48, [
    413128130850898355485492391548810646030952171349358231703620074377114265132370690118327502187128007153215556247827587573200412922903,
    94753161567359527831336685855926036111883226651865078863888629748643473252025056118918315549315068794966138848285260737838997932858786564800529,
    50611234050593080844035832716454510101704295496037377534227960346400037785412934933253770168782898703609349117543840385167959208563000213504]⟩,
  ⟨57361, 1012, 50, [
    50611234050593080844035832716454510101704295496037377534227960346400037785412934933253770168782898703609349117543840385167959208563000213504,
    38702756688425975434760623633644785972615321429676252123754010522020335985660346483204700559106210408582945332876153002997019265954148777984,
    92328975139083095408756314358757593226409140679115251169441750837829522538478475044688419507700995312771807097113003868706066050439067992303,
    496918958758448841253736614176302220693791398853562402394986086955427317832940636717598030491084997355471152666942143754199249717710118485771264]⟩,
  ⟨57835, 1013, 43, [
    496918958758448841253736614176302220693791398853562402394986086955427317832940636717598030491084997355471152666942143754199249717710118485771264,
    51858652149826982131905028911181368444741682144753298856679167589005487312286192079904489428067719709225145098576370595531664082732548688458763,
    34031589201641019911539149874953619502754490348124870878461264313518844008252071941999274609965102072074007319416914034337746503460317228444672]⟩,
  ⟨58316, 1014, 45, [
    34031589201641019911539149874953619502754490348124870878461264313518844008252071941999274609965102072074007319416914034337746503460317228444672,
    56597477783450457618679699596613859198855670355525770298542766103298060219377824482501181761676231269577643669851777574176662474755051386005,
    47170645574595822037000522914502613911992204141458747852377444965300483575363834449261306244599337728084926529715092491028627792896]⟩,
  ⟨58809, 1014, 44, [
    47170645574595822037000522914502613911992204141458747852377444965300483575363834449261306244599337728084926529715092491028627792896,
    124991940555232043361831610617743848437545090462423590694868487791887875137866687648604190187501405778299284620240161332381195652961619775848527,
    39631573475140062665782647840772340025058294670005280191855743147709704471440708209416579741697589067129694418282548925576114437544770055176205,
    122062419234823676523241392548513109001015533596509159107668827799749005432753004512160809126780077200601187333283710584042123269758467988607]⟩,
  ⟨59310, 1015, 47, [
    122062419234823676523241392548513109001015533596509159107668827799749005432753004512160809126780077200601187333283710584042123269758467988607,
    207409556497827587502630718928622621280872574999821454155570216372724049676682613928029232431741374804229477622496699607490596721131520,
    204255032154728959392222263050484459790018316293530327169937795883820995106213557598354263447312799505517226744623662394092196876184759908234240]⟩,
  ⟨59816, 1016, 51, [
    204255032154728959392222263050484459790018316293530327169937795883820995106213557598354263447312799505517226744623662394092196876184759908234240,
    70117399388837407338564918320407884551998903026881144556166559809230551906674359996449296620452940112735716728852653877182220694728855299031143,
    295751365959045835678026987130559935318149724191840184764615587040748047090769943500202433557342064358187476592797824953622546700440330463870995]⟩,
  ⟨60324, 1017, 40, [
    295751365959045835678026987130559935318149724191840184764615587040748047090769943500202433557342064358187476592797824953622546700440330463870995,
    57955855321270524176415644332384788223851360967217390091654242704443006734348581423467081598699541521649968270673065013392570512526602791844875,
    33534408508037628109061194895619890481060035620904919501590293590511342286503022370831911579975435171697455353406159072556485995073414099905553,
    600621409279737734014976738268343286090760525806772626490123185953585533222992206956716760971802516057072448692492103015532191006382800061346816]⟩,
  ⟨60846, 1018, 47, [
    600621409279737734014976738268343286090760525806772626490123185953585533222992206956716760971802516057072448692492103015532191006382800061346816,
    136693982897761394184420318377685948219841943977400171714740072876458134232736627833575507322685606419764248201509400488667898457652184095,
    303859690555725960197375354752734200757237712047686090412691390415918967338259902448333264741722739513569851822294005840284065747539081]⟩,
  ⟨61383, 1018, 45, [
    303859690555725960197375354752734200757237712047686090412691390415918967338259902448333264741722739513569851822294005840284065747539081,
    161575187791379515017344049402115047783371348478615595920694383508779329564764349599405359263626901625590418317856826522584427027615458953020416,
    51936351203939341966417583767298064410201662187534610308534717775793275153272603674818646435346983069474600699545363278523129812808832054722583,
    39632233751217441614155460295697992820979386082850928997141853393989613081296663889384324705145292723555202463098009032468877784501729120747533]⟩,
  ⟨61932, 1019, 48, [
    39632233751217441614155460295697992820979386082850928997141853393989613081296663889384324705145292723555202463098009032468877784501729120747533,
    326198384272535595992407430254127969490895951392779028679865652567849838166518431760369857604470346077938249395434063651042982792328975554202661,
    69174695115796934056327169417847278414007157601538809760865323201260406739054082262810819330111312869818515782803486473227781428005024301085]⟩,
  ⟨62492, 1020, 50, [
    69174695115796934056327169417847278414007157601538809760865323201260406739054082262810819330111312869818515782803486473227781428005024301085,
    186020186498917230572023526025280014133574519365704519205697816672483070312805919048695500711231678992564290088505147292455018757846096516481065,
    143316498472329896432863248132615606512348559630010983036930069568729989535244371094185651044746993700823399625226306748180708961846546689687563,
    33573166203684346599824630851795767690551719675101634320972617278831006054845860183880959902741406743024082257207446279308576560171557859634273]⟩,
  ⟨63061, 1021, 49, [
    33573166203684346599824630851795767690551719675101634320972617278831006054845860183880959902741406743024082257207446279308576560171557859634273,
    112997054826518065779328424617931724277168340463033532795364698942196297614728735640115065331890737659675525498720149551542397865314515166429184,
    222546527512761357178129965218423503020410913800965354943384472629259010490327387145016954749754244455143351174756824154998507184502450261327872,
    94506059665697467192958712251062843180044484420488668306021754124097408682513219251524583359441489253887852676820414987674425597916254225577211]⟩,
  ⟨63642, 1022, 56, [
    94506059665697467192958712251062843180044484420488668306021754124097408682513219251524583359441489253887852676820414987674425597916254225577211,
    473952829347010531390547018908807147466845204715190201287596108596342701788785947915481607617736510307256108497021249036010445966329183232,
    336415881094124492653879916964169839982732775302782690447558706377112274968790384864622538372508548198453114819544288600269608851854884742144,
    86578121535911463557657507275756179931231838243804223655172522004945005295055040631330861755904430585162132784346576089863368851432787696657]⟩,
  ⟨64229, 1023, 53, [
    86578121535911463557657507275756179931231838243804223655172522004945005295055040631330861755904430585162132784346576089863368851432787696657,
    57973680038772029794845303331270884991310597754722827421453691391378712375440606248256705413897931188319157233415185303938153351773568100273152,
    39771617819621905534054140259623027359839835464923154223466135923230254005910286498400499892512299070647741127021712965243218531342355974353933]⟩,
  ⟨64831, 1023, 47, [
    39771617819621905534054140259623027359839835464923154223466135923230254005910286498400499892512299070647741127021712965243218531342355974353933,
    70334854688897912494086269951901139325680955049479219641984185847826126269240123548426374639701211790483668294406244524970166184030861771407539,
    32748445561914355066000942832839858960734212746145465233521203345729111815983324419566095913799418366969940225515094885931449743928232789003,
    33534408337684801917234230496771735646677293599437386848807401429059028154706930999115624922922512168029644727955578891269790257905984377728071]⟩,
  ⟨65452, 1024, 61, [
    33534408337684801917234230496771735646677293599437386848807401429059028154706930999115624922922512168029644727955578891269790257905984377728071,
    32086373611254874552128634715964890446827508496453638078761759864004958874689475278539303503021611337594414598719171517923231096252661760,
    38752133726765830200330487385561972495140704570140956808115022145754980725442742689445848294774904364220406969102116839023664739617292156928,
    324545207880339570316473246060738196334962526968511370720397183250585885224495911654055054745310408107151148323575338793329074994788371090673]⟩,
  ⟨66078, 1025, 59, [
    324545207880339570316473246060738196334962526968511370720397183250585885224495911654055054745310408107151148323575338793329074994788371090673,
    63771402965230163167464078307021708398578543416901145290759799207300796533176544723196551815794330227014627322392012796068667345920,
    710319738530866381093585069436908305495016941869914353557154080530694253476126253220329641880098020704256151312568119203707620363944220093854720,
    88465460104694505208110247944644669035662682244544875920423865188794773293640528177646777720574558961959241008365131444918596057213116739485719]⟩,
  ⟨66712, 1026, 51, [
    88465460104694505208110247944644669035662682244544875920423865188794773293640528177646777720574558961959241008365131444918596057213116739485719,
    128016650863236315900434065220372876534300004977234829123270410443160207922724802651956861723015296372771381953405420833415609219295071961171,
    300745512798409905594375409058820129168735998181035220674255176916634408543930482823821962000760627034693008246655169358711920807892930821120,
    131158044892068058408449007141360329254419255732938660698030542000078298277974947458058710621905957159104813141637458758566073797530235379526656]⟩,
  ⟨67363, 1027, 61, [
    131158044892068058408449007141360329254419255732938660698030542000078298277974947458058710621905957159104813141637458758566073797530235379526656,
    39664321838780935500106585093496989363231532348083510903763493241061310606926341261829900765271640934973482079483578442711733243217005218103307,
    33534408320649519252890692365045497566563780155672514654026444041452379919398352199940907394946803824146278791521790825546163067282272517368863,
    32034849144596387783416228386312278991840727921049101431452873188117053007959450465645275078701581669256783434491807003381349482177232913]⟩,
  ⟨68022, 1028, 65, [
    32034849144596387783416228386312278991840727921049101431452873188117053007959450465645275078701581669256783434491807003381349482177232913,
    50611424277537029569888022301828311715324706615889558614005056077694965344457307660508253733079343500446252774500498943930697550298872807424,
    212285226809077045428431155872846213927305848190820067840357426100801029939544851825884418730658620491391216456794368726615713525407940627,
    57961943047717474529459461002758129424263558196313666721781241153222154558598981708140454746977839127393704886139067950851882141568962039827485]⟩,
  ⟨68686, 1029, 53, [
    57961943047717474529459461002758129424263558196313666721781241153222154558598981708140454746977839127393704886139067950851882141568962039827485,
    423753014871777569332348873497578236115070157452510761379893181302052247128702215763961194365109133177267141402909381359208097747319912029766656,
    51825903667602107410765268838206880356523408311514247509698309394459898404180393866761479783455700916984600358154104422744629253056652647596163,
    206459138029952618829179914678061159417053242266799056912697909439073230435988398953666242104177945231102216849130832465496705882182923487,
    181654441367000228890855265949741234696831530979601637096185035057171377191650039332764728432001718338673307291711652094712306376696983106603]⟩,
  ⟨69369, 1030, 58, [
    181654441367000228890855265949741234696831530979601637096185035057171377191650039332764728432001718338673307291711652094712306376696983106603,
    179976720206579403067117484970531983366534731214913849457267269102727339562239478059746318435237066605981306360726200586871126573406110914445312,
    70150708868798456169198516714322480300645526729265912221775122114619383256916672456094516525550939523366256794516691640665743275439720481467403,
    33534408255347602582626129866040554682881007364045876546274405707648774037218950300766800525605663332506884917038462899892584715882640021924901]⟩,
  ⟨70067, 1031, 59, [
    33534408255347602582626129866040554682881007364045876546274405707648774037218950300766800525605663332506884917038462899892584715882640021924901,
    39631605495803871579402479683966434939366061076983204589257813452832250495664298053913348539181796193221962579688735150972968984628880917679117,
    86741362078860051748189685001821216484710258202683643862776004479457637945815476622226891480334693691204539713383128106677719750543611632753,
    56632366042216506517638101702299544937715057056977065538238012291852128616202498517260506456617262409418111846931597943748991986616541118464]⟩,
  ⟨70781, 1032, 65, [
    56632366042216506517638101702299544937715057056977065538238012291852128616202498517260506456617262409418111846931597943748991986616541118464,
    314096403392126345833989115170252046845111741852281242279399352589859605448266796863495098197843427603061442254310538844781105098592676425528320,
    112797610311752733015333655496349726595326052196412178089488687435100725773593498925220256164291239362360556852436584778701696384237152412703744,
    39205681174618273793732293416521210685553568376159140766089228709083077761146107811662090987620876999232139703109758182960047125506541223977,
    37877981361974805509450855239392508763738168034753610708793580734097006388296232422061079104079431887574831561810739713636319717155181585]⟩,
  ⟨71506, 1033, 75, [
    37877981361974805509450855239392508763738168034753610708793580734097006388296232422061079104079431887574831561810739713636319717155181585,
    783536648575838981570803898163710148993730679439775746614249123865564449139098828495261732341603977543840041495247479108294840231209863406944256,
    37023829772522988551742981522597504083487842321937383130876214043686856184783779799846158564673104817600546533899980520149088813986816,
    307939587881062031234409695037730805060126851346981576067486057307842960832625037848226620184288971642279580189548763685579417558450647909531659]⟩,
  ⟨72240, 1033, 67, [
    307939587881062031234409695037730805060126851346981576067486057307842960832625037848226620184288971642279580189548763685579417558450647909531659,
    33534408422913895591725541662281115044458205301250454982515723624930556288407865498841096283938143378357770344836296785306797070306166866717715,
    51825935713857836513947742201023959098111209203056511297932510528964547202503780928045497270463478102372619727498074115076252441144166599209984,
    88408894491371569615829085175522919163832098081260204959929970721338726304658361189851767861585009602825781551160792890976597314187493782909952,
    39950176199922449372592471521588720893988226768195608383188735379417232857923152489989877031706125467143571372171273932573789823262819895738381]⟩,
  ⟨72985, 1034, 67, [
    39950176199922449372592471521588720893988226768195608383188735379417232857923152489989877031706125467143571372171273932573789823262819895738381,
    344489830259526798336167820406892470442893805622764084895073474827568223162534560697425008418532696322908523365444328662398609707906534833389621,
    119233511610749980909767888422303581827826361681859890605761979910878752910436900271635934822310287628249097565837200860615787323225800704,
    265054823911546833158872777979022436614917184420852392270370636418871446624712819044515868340097664998000111702613506166608143885186482863104]⟩,
  ⟨73742, 1035, 64, [
    265054823911546833158872777979022436614917184420852392270370636418871446624712819044515868340097664998000111702613506166608143885186482863104,
    253410449022583214488346471127963971260485331668795584910527393915216735566852770231845446314808236427000965286927916350167607030639509145387115,
    204293859825951485201588982932555880666970941572589052788337834396724148718509374448525400366485472251088952191837567274055044763447591977376768,
    37795777334821754129808826119812202383893449871281093134346003110624593651025509823752678335062821695362908846832004328351595476577963039,
    588409184945377356994475444928362719718974623057886217457047166712085996823586394411575298699119482129869387099081707909181300782663076196384779]⟩,
  ⟨74517, 1036, 68, [
    588409184945377356994475444928362719718974623057886217457047166712085996823586394411575298699119482129869387099081707909181300782663076196384779,
    33591372096860465632627120577267912156173764929000503987398620786366532574345063094751157624187713351086347854310472137720550527747381764566045,
    241549589313825684217866596715930080205944842548066321879137214611071687444570631353811504110007680727045533653092251557676809985885423106415616,
    387560045883164358763299005872478669834344176446305266783393401199093261228631075128952000777888869699798061359603733625692749713831932784170001]⟩,
  ⟨75306, 1037, 70, [
    387560045883164358763299005872478669834344176446305266783393401199093261228631075128952000777888869699798061359603733625692749713831932784170001,
    50611350543904097397020722747688731832099562115965848340777063937177294221187069059946043479521855422508532442008961453126836270426127073280,
    185963603606843517043801990519656378236151935960553784022022200127140812602520291056377581652651187895046037044274077114696138649484094577049600,
    39631573423914893179850096236832697545376441607820955192778568832083594572616203956579955605931374071429510218860901045535848641991023518647309,
    128016704841569651746709680168695389626751789009857615502738389516614492974139768943566187584129437421708144200604735246750078334947718874112]⟩,
  ⟨76110, 1038, 75, [
    128016704841569651746709680168695389626751789009857615502738389516614492974139768943566187584129437421708144200604735246750078334947718874112,
    52627132881435652810048259913014745034712613755026075943908673342715834026930325247844706834524272674863207924533491180712834503076322931113984,
    125673648409408778959643950048989608608502810037545012472990121289801911932696450091363470707900834967013545789428465913827983573207093324283923,
    58009455040751243575868798082919489462570862008238137040154565869650613107077533297876505092511382451919525863589752376508844008092770208055343,
    94539386637940334097825789918307059276125918097351078154264044118407367933876573728747984055021987900633938959275475193907252314771200249167883]⟩,
  ⟨76924, 1039, 69, [
    94539386637940334097825789918307059276125918097351078154264044118407367933876573728747984055021987900633938959275475193907252314771200249167883,
    33602920073499706602068502483495059041807806782064895110419081617273306704971858804614640253257091035396108412493545837440369921354920976460800,
    515076274974694426204178726215398526526214419967524381359641118619728136085049488184982704832614034681938323164456478299508774284331186217984,
    460428258979747298427765164011617374746230081325656013502293449790322126052257133539787841214485461004250753925060038844877702115534401614918656,
    783715390522430663689778141772772605077694385643946951175999520357006594516798795341569729606955673977637195208713310557972424776271439855717]⟩,
  ⟨77756, 1040, 81, [
    783715390522430663689778141772772605077694385643946951175999520357006594516798795341569729606955673977637195208713310557972424776271439855717,
    62453923707427526665178785190642928095785029023969182834129093100398939141030088544376195933193134315061054863355973764331339813,
    31231386822300049291484468717745010456329865982707194072271507502794999398298085500256469961109457186654647957506320483375353928089709,
    371937471907037884212364419943143892827331040741152987665062714305939784754381777203079925197251118748327247842178251540341570730478592,
    39631750741362914915692654118498506637070494813998709745136461092664112540155319730582303225671783830209024466371420913450767504196292594106381]⟩,
  ⟨78595, 1041, 70, [
    39631750741362914915692654118498506637070494813998709745136461092664112540155319730582303225671783830209024466371420913450767504196292594106381,
    582335943920246180481052894825078525722981019423090129922445210290532842067974385971898825671372044896630618192509045618422345793871167869750289,
    88459505927005202880695312588021049494579857284645149860066086685958834010294923862674762801839498388662013048454386638140550995519431781669888,
    32803734217575404169640206684414931369073914035660793249915632715932514786326904286263881111867840059233409340200117845923714633959847493643,
    33745784708241765498097611900591179756996049181757221985327553495990488548817031084017685910131413913282690823380230053826321541142683358080000]⟩,
  ⟨79454, 1042, 74, [
    33745784708241765498097611900591179756996049181757221985327553495990488548817031084017685910131413913282690823380230053826321541142683358080000,
    70156134021348816113558066113443775495984319441961133136740039892532991236227039590739103012223618640909683501506102833422360394461826996257853,
    51825941462969003227036848835425260461385431855418256173122058162234738109571467158932215030691374906087527046496607400447086046758211259888921,
    413821320759552622677228486249180928545859364521773736426660474379319544997851301866508191870190382747538810288758482357826734454364320038953,
    49462074026174025860355421398078368980202036283338986034750345452426522710149041956857579727821186535091392139716202204374641358676178083]⟩,
  ⟨80331, 1043, 79, [
    49462074026174025860355421398078368980202036283338986034750345452426522710149041956857579727821186535091392139716202204374641358676178083,
    606885328658628484327081382024786726606981919896956739694903585310611333895194999306435874546195919260840169549147393686085764757285738585784339,
    57923069278953640644470953912090983906972652971553971258734107502372777232061216637668102003589506040642592572425282016701561957793708743065600,
    295712509555473481004451545005251286735925809880265392642399809960030553577846571673133046504708732721497279381582796226110138536107218966675485,
    407951593041262075318942931178331225954119459046523916007219345544698904673973842231786656975078308962745775344655833279476060140715110301696]⟩,
  ⟨81222, 1044, 84, [
    407951593041262075318942931178331225954119459046523916007219345544698904673973842231786656975078308962745775344655833279476060140715110301696,
    39631573497734455942215587345234076381116702614234802745459691539536063891637063889124010199957503894668783964158460031269531373158913419772941,
    33414229833672381115285572358755167406871253900243698196027976698432886705956355824678704944401560888081423628994414515589835481050921304075,
    33534408255347602582615800553774782999512067187164729940475348021263960756892288606222373188332946698889726787186414498694479707621552969231593,
    551861951480397796206347375148248354468952728586340012933931287476454579138761687736581311960744793162294595994490939519418811812102845968154727]⟩,
  ⟨82124, 1045, 79, [
    551861951480397796206347375148248354468952728586340012933931287476454579138761687736581311960744793162294595994490939519418811812102845968154727,
    180631613526622605765887341022766100099606866286256605882988325575230671667722549827190725792404387346774517974537346373171592724893855935103043,
    38702773693209447553405096861142099820490974175792974369774470812302542823919145793596962521030650742601722397405035081381695171889353214993,
    50649029766514914579116928478512646839809111438100644452181174099789163405761276588980240064445816565185419271598202847743715604751410266263,
    143340100345600305561135237329084320863767986771198203720837203467845185036516878143373191275240114404675524981885355312170718401533169273771008,
    801935003561563495726186317780860236630864327419108392991494447178744361026448694784826059328240709856213128078802189433086116454430176650998941]⟩,
  ⟨83043, 1046, 81, [
    801935003561563495726186317780860236630864327419108392991494447178744361026448694784826059328240709856213128078802189433086116454430176650998941,
    532962072481796699140203410357382480616008303668923413497884175424847593275179622414402642573712964035308948553008859547243529401384098088127,
    51825903667355830152786806640691141913239365567121435706476661338975801778933694329481133681198877021894188553361858658030036197467866839182336,
    332296073412646766534426879994385257609211755301226539072715883378674575405248384328062326128758161796112137112811946292294454752588229032103009,
    417688609860639853300310358412336666940518481136997719284109980307865279501840343895141236159766851480541856417208936167913628663432606839233547]⟩,
  ⟨83979, 1047, 80, [
    417688609860639853300310358412336666940518481136997719284109980307865279501840343895141236159766851480541856417208936167913628663432606839233547,
    33626699383195958516731671191291044017349958800971363379885560899586017344835796110400293040876060021664859967259772656349839702692834608950285,
    574618343943826565125203900151788793763969349906292488151693091396722455082563537439714159462116893581571582302475809466689882943170652871943,
    70709848230944605164271291622307929192899961355664145841785122446373044524349905247570971754829439644177223677507844883431637497117350848102419,
    58062993981562927981049173597668185578011201502813661832979588995583322749355066689875347645723935319636177703674448737666392813481616200481792]⟩,
  ⟨84935, 1048, 83, [
    58062993981562927981049173597668185578011201502813661832979588995583322749355066689875347645723935319636177703674448737666392813481616200481792,
    326199117093452877325958923765301252677577546962305825766444565253843921655160872899623358726430517431510985986441772290933098193404770951102631,
    88447597230993617834938184198305491093627866615970851130262192294078148735068999282039477521493121904856021334732925176980164536881457477451776,
    110192200833025422606085753752484375347877011972578208031514911158062703725519337300926368989392463792419154468867731026489941236358602293248,
    131211113610183308215416074098170476790279744240313192674503490338228896930673742562140988594239308107591374915346809717160418119075785205666816,
    824665438849551584291990079995913967624484658123500471736757452924970771393086007894452877909020009745860009457812862215423718851761035818021]⟩,
  ⟨85910, 1049, 88, [
    824665438849551584291990079995913967624484658123500471736757452924970771393086007894452877909020009745860009457812862215423718851761035818021,
    485272420634558131967537990900008622131151321042960105222983541650172724388250762792817440167597607726425784738460766055439626660829379690513,
    33030458986889673235843406999125616180621502492087065837116916737753153387768234380507232104591404589885591575410177744775219994937651174411,
    33534408303614236874432964516588493758458845625365286718241846937745310396809011238950313515656371643068397191469494555907486344515216057838719,
    467441837431251974416017748845540683620707394564954855405288576260672793574624938458318973293485474724589850653845312358639089803371834507311,
    39688229017728476647771380762895834021721095235423255076946457588534941456663122350619937233690036112646889068524480177765108836387485313418253]⟩,
  ⟨86891, 1051, 83, [
    39688229017728476647771380762895834021721095235423255076946457588534941456663122350619937233690036112646889068524480177765108836387485313418253,
    52454078395860163842018645021612887452000537007564951407607501983910314005938581392575105557413232258312228108430213923163066358271818409705501,
    734708454354023784910523248215170946329849333976343848435982104500736337226196456835449475588577567768449973115604505152232718987720156413727744,
    49456264688207005509690500825166506603708236377424245220247033880193702768625545745238191150910924444538177594882691809246534067411746847,
    47197691248997092306811987231892868353181061990818593250568992179938652325481880423152287498586251302314293698086536807866966342699]⟩,
  ⟨87894, 1052, 93, [
    47197691248997092306811987231892868353181061990818593250568992179938652325481880423152287498586251302314293698086536807866966342699,
    38932389459078114593218647056568230648346421434493029371846098679019066094384671049807656572384561890323844785285249072950126747608863998179,
    336453699884533898213585928956542188797996794260704738673767274335580809629780319384164263294305424025930355143785434787476132568958917192704,
    204255032100833805372855146528583660727416641269903844794019999369132027051382540023949983271988920680653135093251585874947855020559040297084103,
    185996285171270297403507109635741941765201286921961144483829692937953601103535825620560714977316252749531705905950830750236953520377907998897163,
    33823190002610983453504443536164898825495306528094484047827813529214207177013939084319519286648657350593008094087899138822228543700128292154409]⟩,
  ⟨88910, 1053, 81, [
    33823190002610983453504443536164898825495306528094484047827813529214207177013939084319519286648657350593008094087899138822228543700128292154409,
    271410217866473207002994030475655884306378988524692291565327992507429869094905058913886753272598081459047901888795653891058368670741173068890112,
    643575429418629973119250660349096228431555461431040861387645203490485672238293403028264030535867100813379853222103841115063831386944072127086785,
    70117399792119493124734609474567750017247955280914331998788454232077409374535893340269311771428461642157767718841956454336680788665607512945664,
    39631573392683495124961683581404360271756383444691368619790812814882586338853047053743331860431399484480569378417198877421382920361157242133517,
    820119691471034998306615889707139730883556049638093910601655121899029542794798049325097646833643282262445432263235188871464045337291422139753683]⟩,
  ⟨89954, 1054, 95, [
    820119691471034998306615889707139730883556049638093910601655121899029542794798049325097646833643282262445432263235188871464045337291422139753683,
    95199731296601979888511276401019101498352004893144761108509728983208817735612070821205273465733062367383925602824505476957661706535866433798144,
    66869193180593214583921846660358595831053430776085765229917813498807560347101400777455441293157098446710593793673941820640151765517336725,
    103013930246642774690725103557086003336955543967849461065079068305402610872094307361629245252702933535283202756736519459278163035273,
    51864606583073168436057877416528373701009881416338266299387710122227120271601738736849973061852981448840015013043417348287979760593894498107392,
    32786241175526534416196833510969196967474352736416338575468672054416197813539494645622796595135798044307306646529943523197857832449935933451]⟩,
  ⟨91013, 1055, 97, [
    32786241175526534416196833510969196967474352736416338575468672054416197813539494645622796595135798044307306646529943523197857832449935933451,
    33534458069353140732720726459716390751975163985145678261042081553049298505852944693940013650497680671813095377793404256069316901262392732691479,
    88408926509231768115480569718574165749787358022942020145192406091815592845395728583811801934437469410048868102734631039512757909828121527333961,
    253032530548125549636563311106582455234924560666632557001888534258425443340713518066502107778443171127509853049835008736696304388720057062132736,
    240906497597487325039772090767679087170174486404364456029904783884845107243352115451436729566570721103848757304521776062339413067633246931517697,
    831889669339760716361609761109157856579518226943622920730260273501675213737608356025772362301752625109060430977122182152539168656542720]⟩,
  ⟨92087, 1056, 91, [
    831889669339760716361609761109157856579518226943622920730260273501675213737608356025772362301752625109060430977122182152539168656542720,
    509831210865607547976899552309269055497840142236258531906648044417743374905905983533358026798850657638570394308146647217360202799443236356096000,
    39878800404381676788745099599467403294360742418530771730093048173963490187171016026950602852020404877798230732104622354392241149426019307985933,
    497183923388817849040343567872750930053135659715730798154544004484284306703913640722345692293432446227361440134297195303982560629273969400217619,
    57923068921099026543709925663091374275141164970108124983981065516815443501351353307729989984995021049926347538658221889914812223687261586194432,
    169233096918114271671813470951943270290545540180135790334755031022767309883575621745658363014353681398614163330898678117759429184571]⟩,
  ⟨93184, 1057, 106, [
    169233096918114271671813470951943270290545540180135790334755031022767309883575621745658363014353681398614163330898678117759429184571,
    32748445561863051800485516708686393101910332972857584454688690842314713954433629568749461358385196836913929753056390539530619683388455527435,
    33573195277177864842588978135828691577752668559739789137827091028210687636702994646685578204721246718757258533061686610000629339067285803904000,
    307906871464634772796928722641060172282632794882411337129870677428205288512481962143534739351748369660496368138956558373802747907751005325909029,
    125489621700651355371658387188021792991515494155764613761474376681355539921602112054580048192345589953189160767054750054385953634027019997020160,
    154126921818507876756819372287122632075029933614028595724223718320502435727320619812148933149671316726133217976100856937940900093080122399]⟩,
  ⟨94290, 1058, 92, [
    154126921818507876756819372287122632075029933614028595724223718320502435727320619812148933149671316726133217976100856937940900093080122399,
    51948615057073571136966072651177584133739439686929105892752097762215953532229521317061435932947884685459352995666949632396555330825704557248512,
    222758011446648871039706337314880320176191426987960188594892958004333610544967130160110860574352995462821190068435498473137442299711833331747953,
    112937530002819594633244837785646256929282614313009572815990314692607554087213988504879663239662291014146270825038707677715953702104344355192037,
    56882398593873992898606635001634939535109817009287210593489671956893996170046984164436043755497776033975019720630915807641552000113601426432,
    39717977072959102172550329403701050793965601123536441889901507722495320441275227233412448058789631804438004358615489395722206344230124112614413,
    161756536395739266976363834928423895033352652692464137546434889820624188616046236431233585701425766481504228317817371329979137880834470319412224]⟩,
  ⟨95422, 1059, 106, [
    161756536395739266976363834928423895033352652692464137546434889820624188616046236431233585701425766481504228317817371329979137880834470319412224,
    33565412351742722232301621066572501000790011998468464383467863159064197707876033875112245964920751590287571840184708239157689517259052053515,
    33852961316841311684535802605918111773304130595816146934323722642814888869693123831260478451436235961367491491408426145028028292191981349645365,
    765411587954337826919091598329935176887628001249842510165094070296333321809643219111509512657201488002731339185032469174421396611502781629525015,
    38702762888115314145829355512461303945171720560069240827364489089217101492589627193435113978427505134306082410073752252546257704821647827968,
    38031268406170343233597764902784643001971271017369128196631479810803382104375833693784221717872776340214166032653076005922828523966399555]⟩,
  ⟨96567, 1060, 101, [
    38031268406170343233597764902784643001971271017369128196631479810803382104375833693784221717872776340214166032653076005922828523966399555,
    94574533841525239699665239730376551814216587331190036801826706890902408766164504095521334108420316282014829392924381433704115253039607747444755,
    57923068836557554998588799637536903185632144634022481821853054244422857385518326482831931801875301719843552474618824859526883140804972933821457,
    50611299388113070046394837424468996021033288522100420533056238603912228915117765762852887260707056084871370152666006543614528224532915856384,
    344582121381632982833999815972700582378543151086912991964192871660462639649052236512922779884054618296234014858120804099854880180139590492924928,
    88408894658884521891535298537887749062381177316047387708025131914307100236287272813428690714070072087433742722308468525281875837996298176299049]⟩,
  ⟨97732, 1061, 96, [
    88408894658884521891535298537887749062381177316047387708025131914307100236287272813428690714070072087433742722308468525281875837996298176299049,
    399364316618007777553367268806945388248546936893858437639449559718009292350447567759404410850733561927090932377761239993970864496097537287013376,
    39664321838245358049840161910058806052396119523004792077341714768130868470179385151667396738257822498859667701753381842756032535984862679531531,
    34103235148449921209483310691854810250328121742159405699887193169833564838250484137380346073381996067261389591066619245693889834112092004690944,
    423753009025853224751646657730786572530593546321689251584180164246614058452521013442363019372458534527718873291583787056777580549564299698241536,
    747734136679448624789523703664731824790943265615892612258892879207020658279037728711148946140945640469348688257943628230045582325667646688256,
    614694791614846606698816971231498912513124579726807274857296494389731426015592994699489355204000229218975249085525162264938738688]⟩,
  ⟨98915, 1063, 101, [
    614694791614846606698816971231498912513124579726807274857296494389731426015592994699489355204000229218975249085525162264938738688,
    856690404592300865726069710159700435246570377744956867376858608339666884588574326436646813877624996416373643967200167859572256948691273685925888,
    70117436906477070526061585906937801172919848903212373374283869580729537644247026970690799837300164502107768386562323351072457921796641523761253,
    454238857971432847362493338147413934738480333291028701537941464868933727376071326456340938693843352471076146640979006555567562433593296114912285,
    698125492575195676742292020152102704192153667420880781902588668978610627439594607110447456658753824998824366623338871281473544309953523707032576,
    36044867349631726654389539609247224392616637536081483573874660586956123003635507518992685487291424030133507014565483504429380403289,
    66869476058407276860782853780937020536054916178134892960118382596554783264583826991548318320810511868549470240794798206222943853848067072]⟩,
  ⟨100122, 1064, 104, [
    66869476058407276860782853780937020536054916178134892960118382596554783264583826991548318320810511868549470240794798206222943853848067072,
    216482110875062518240449127425548827338251794438051665017761280195667275223239472237366641831768080484790518100198841203839311248352501183807499,
    33534408255411374490983737918726767317912570527381145513758057073714945820926587764964691561550152972542908664700187429064211286035244642216977,
    39682216607690280493098586859935472027012700795530960656085036287857238875657950343085601788878306110526343261840883913890838065044041099116557,
    58301423297598027022841930478603969789903423649146576117014323243734161407755035118853361066141571764646655309542832138710149541383753813721111,
    110290508024662052224276348640953780673495212111402060786140444854789305295602550671740958564171067017736628537873004108761978722217574268928]⟩,
  ⟨101353, 1065, 106, [
    110290508024662052224276348640953780673495212111402060786140444854789305295602550671740958564171067017736628537873004108761978722217574268928,
    86822339294558879301095499869544141891585314249636066226364756352843959465639190396454406561423593203301417460499296131631377150024085423213,
    51894502737837707798103665829062419902985863657339393976716764129667261596264204633799108459592682731218210812274256891284804488118008975196197,
    38702983881465318603930987753392403798854659603127597058447173140631954951109341792164584758832675704356155047228981231131196513928183051264,
    37860946079374749484652817272950777506421431560873972154719211589058511114385483346333612017686657659771737292505176514132903479395483648,
    387169986220878203268348043445333867821402366387255215758107934206751287903141439854141187752157080602447332497225831062024886295346275681304659,
    107609041037076687840153772112224419622746267673827509499460353055516964121150048526622784276469530291259346400012928278963502569481057280]⟩,
  ⟨102609, 1066, 119, [
    107609041037076687840153772112224419622746267673827509499460353055516964121150048526622784276469530291259346400012928278963502569481057280,
    112830303915034580661203991288845660282404084994509102839384301399430083419391426785538570295898696466363919063598785578915489095176970910583819,
    33534408255566643538732957573392682474830532583692140870796940787656810400808904786321737536534722255954364773653029569031393922087578647931904,
    56597477969254387431253703730993006187841387916791869220887120878519656013472737840517540370899487432666645246493736960337279315666423289011,
    94506911483691830271970750668503638086748734191095511001111955068802034492070819302472393558104724944211699666507116432734358013356549726011392,
    39759645507557244340110559496673254225916686904294645290126523224644797793157674040517264258250054298662663267674500205324472140896601088482317,
    88408894491601005359934223083354914081259234600532920631399711398147045809114276164044694482816929198690246066276503380859063860146778053657600]⟩,
  ⟨103879, 1067, 95, [
    88408894491601005359934223083354914081259234600532920631399711398147045809114276164044694482816929198690246066276503380859063860146778053657600,
    131181739865430754436440327849238164421088014120610515022219978586512021204276899078265011299609695961602189918905359485439654357362550911271015,
    70117779942854637686644853282979170180276598811793648152971830755801411205345074724985963172866359586925524530063921557203965819999532827541521,
    50611288025856141771237541097986386103128767608763830807789780237535678102599035029662705961378154531501278691958796834119015129694987195489,
    38880105306895699742426179546696728172282225392885032343124653539605810278071173968874617782467474767412082331508908738237744699488881278229,
    692168206059785170203399473040360755002247067341767374663999384499059975195426908294762329359669827014782871647514232777670584316567914663689235,
    57955884224586173269836746049846938441083146710805838309885049201177587655862311992647626467728170787427560316837305806285467099837373776675851]⟩,
  ⟨105191, 1068, 116, [
    57955884224586173269836746049846938441083146710805838309885049201177587655862311992647626467728170787427560316837305806285467099837373776675851,
    33534408292875687159654121567265880976664173819581226169612704606538311271838702733222408800443177247859580238681746742208755742124132687424512,
    235226046952901566253473087858855132103996110884439696335580833532463119058513371773978621282379612315043739961772212424155818286963797074944,
    157837478028815026114991259090814480598060151968566294886238458498550735100909741404071109372621816984007283863123321960002176346527486705693,
    84313339188875107611532731387591974969855908424186707160782919495116778140946645059718108830474307622065175965583237175675630333999490071,
    199468591417544208038189336420131904271044788612754262114152819007032416940296093386799465281135843162434855456308247946178925217994705469483,
    39631744957957162736200747761616531777477743759211711635479228593085089972957191717498332007579669942725105693413418561872045448650446074983437]⟩,
  ⟨106526, 1069, 117, [
    39631744957957162736200747761616531777477743759211711635479228593085089972957191717498332007579669942725105693413418561872045448650446074983437,
    826234350441030216439298420679643001303573229238093878579856642039834752600788765004736614913693009761355920944177081958927251455704678530067456,
    161574966267434253685228709725059714482062753403797375486104871341351397110375660003526455384634509028046881045391692692027980623655986107796527,
    332295782063615117619791629359727992731622530992817968782457824248328917527979115466575513710148242274079493023266393436952060941926620361544777,
    527461660963411481425147062625356523368369472592616268523990083859689388472560595082407791375014418998308718929917859717029130473568696351743029,
    179899646228571243642659028632496921316403039296361654458195821161517419892236559490133573872022122838948118865203998650932648879728251666238475,
    33620782861987995323448457654368473360809031665315285982188082316422011519783092563116825255242418538508082957806645156352716698816792437468160,
    326198366828375713557589693637227374911639450249035169882661110890591810614756523411101085657294232733560007480295092271752589563015758137762833]⟩,
  ⟨107875, 1071, 112, [
    326198366828375713557589693637227374911639450249035169882661110890591810614756523411101085657294232733560007480295092271752589563015758137762833,
    271374459882408474214953621051495013047493984214965686009566912356372515568918456350142725458605167997118836743888620725019428732841729340748800,
    503020699891301247003911659408124319666420519510079899141922607567797418031461090678538391611327025978020726372413764919885116714449425547,
    181724271879448182496575046234920411818727802995797002215241051126475703634087404426675895730527462998099421053568579526220286367089835400192,
    240838022956535443843752314113779977256752527943718322217700561798538561385051444236722143750190541873204239992097738907793443913366787344844015,
    51825903667408120716424988247373981485822605250074027297045590777859765878507168585376133271867727227990454354646716877694983034166297742316563,
    39741727255059284479231548341010508451645685974378484160875686364335045685888259638264310278480431783056850850472203335889051890485224308473869]⟩,
  ⟨109256, 1072, 123, [
    39741727255059284479231548341010508451645685974378484160875686364335045685888259638264310278480431783056850850472203335889051890485224308473869,
    253032402826058206144094836828483618421716807678417086823623362491629685814372944245240732620735778031633739524277917129259582894726414850850816,
    288781747274826592315873568013715419734373887545030564999093321906311553197440803282948733032480024941532351016284605542525397824645482151973,
    460368716314626454880801452415431365705407852632313227460840635476372655636774983102414527312562129461842935556114133727792602912496169109474315,
    33534475297702277552022732783780419219119834070590555203794982412157213426199280054324476072736025939448611592567391903811468085967913911069696,
    222585262369569938654891484167680489224696644673817578882381916806810254097869048316541137431011022582344149002645919853276686978078536198258869,
    407904915901244040803019872551176275858467026991176909187646484487350916401213005753460369084729011413899726367817644330671336303306686332928,
    112889846509221435846218516107774434008066279540416004279457162924694211355026108947655830372896895080958655839286763865464806879257470327324672]⟩,
  ⟨110660, 1073, 120, [
    112889846509221435846218516107774434008066279540416004279457162924694211355026108947655830372896895080958655839286763865464806879257470327324672,
    125053522486940357297761269410857813494746012134965990571603459445769898978448848776136035216726190792167752169784297840911856816479024151,
    561150762552399512539620555113832429129368194280526610830591536958631884180120300793667191360011935603544304243061851979149947182345393152,
    56702143305597061609991591680769633729833213887852446866382370233672513227375389708370884884958335457851639748650002664528478103544516313088,
    125060359337955382802340495583271788974143355970510017718464226503155220408233446823022546591450014974877199777358092266494514954932383262965777,
    50666982012462418723755513959571648577479691324870428017532514302870430264324005435221856373611300780778096333668693499140810187030639149056,
    39754330686773862799256334187610272226388001312384668756720839036286689091591231706369114875340617410146360198178233171497315945078097005573133]⟩,
  ⟨112094, 1074, 119, [
    39754330686773862799256334187610272226388001312384668756720839036286689091591231706369114875340617410146360198178233171497315945078097005573133,
    32832759017514731437653802826444643295131864703138649761875888974592685790746198437563656337234549097473269527008561688872597161098769072139,
    33871629530834742984909624230980039645230126513653621352628440930098401205348551810695302348821122524440046894765652856370538627401137953713152,
    52150443027121364114295409401824255476512139748550714301643950016285061705273552108449134997278489848367065254739329321630143350758391652008960,
    128016650832736711341740632044325572459365180961185275630812482974473130911108021875739039479970273974475690777038426163935330155589113297920,
    143322132965922309516038730669531392653736213707663711346185100640525384482506985910380552930296950773462021078685177047064035033672636154511379,
    57923106600352188961881979774610376593879821389639529305028438194634673216430012935370264889768382453276283898311078959260514055260657690869760,
    90159233681257897025955730108335727370627478622543104401104747570738538352217327412381289294468592235912778683014789844380488384545578157]⟩,
  ⟨113561, 1075, 130, [
    90159233681257897025955730108335727370627478622543104401104747570738538352217327412381289294468592235912778683014789844380488384545578157,
    36909778997266726505807705222948241034029824005000640767757547338192218788342475868122927262482799399376639670226096026041318643872895,
    87037483587501260624488785622185284439792176394984950685517574517254557342147520354462583355258655620880616233368847611619399070617465520411,
    70117399213186093484560020644263835218904960690752560346177379119004873716045768160458557266108747026007739050384371499896641942157381848793119,
    515043970503028029267724462919381368262179474404673288927223217504997078090578697208208101741582020752030101923294793120901074198904102220800,
    32748445561862864060590333488201985050369263254454946988435103540717385603405521076267425410990693254435725242294030982990427804018106539019,
    33978207258337808602857466071671335988711479838654451636460955978674996625111094386928180484377997452145693718476621974190959662554660790610957,
    314143961812532926633244399189918844375404253048369939624368009638519521648691696655848151618497514592485020541563124793543500883085704647691415]⟩,
  ⟨115054, 1076, 120, [
    314143961812532926633244399189918844375404253048369939624368009638519521648691696655848151618497514592485020541563124793543500883085704647691415,
    213137024211197173078477702754855841542439366823737117221199723952635308799034107166946368713607014175241322381701168115768146471212285969,
    307957779200681850655222578574261753989623370095291270679785910882263623460684336796984491912020185193000900251112950294155782937996612621919275,
    216449661881246286909507599723885637986941619197907630483092724305159117165902742171448725819921605275827379682016749943033662679129829601705984,
    588415193732395920493995727946616783992698848889661201944379443164992388606967674745519458828304020548673692421469584019585014373980293410368535,
    37795613741923721175166544456155336811640862838888648309017105851668353072156319215638079541813943834127911338439122567104540135413269504,
    51826866123942998608954754581257967917309580563136040011821589251799969654025997270854292088252581402921405582976186371888610566807419351990272,
    68474059448219774464695170262224325148924954540049195454296079702436719146171578321995231850610863790961059371458629720560490890109059609913]⟩,
  ⟨116574, 1078, 136, [
    68474059448219774464695170262224325148924954540049195454296079702436719146171578321995231850610863790961059371458629720560490890109059609913,
    94506109107721352313239884413618887904534900884434284618372687739477939474632973748835237817670063123208921785732346127698917766417774392974493,
    32902600720565737809102228766842541930574878424377118440550170417288054261826023922844630984567727403905115374460118853243800193198612021259,
    33644931351816673367230279945713608705495575954218268706269773921727652314145382706183124243181175793796279112936676511996763562478626720984083,
    58015391859451352369755410999423312532701130545999489332512912840928705822101758485665521410139481645155272570280204336251284514106669834274043,
    40081361546947665815332677999790538297829545543382668457798714671852517962320265164878228229339582036915524608267290526610130825552809070428173,
    966400851869894945457973050666688826989098135869240962917358762679293683627352814640349788773448231571905887743457496867907041220347933502734336,
    51734273780724891899311699821074480247062228864937498147238576694262287534079371543254225986915507629143982047618818168182538240,
    162506718303439317043310892094792227231832036158108597867510959910114655403189420960428222157502448931922907946250881417903161628551206814323741]⟩,
  ⟨118119, 1079, 133, [
    162506718303439317043310892094792227231832036158108597867510959910114655403189420960428222157502448931922907946250881417903161628551206814323741,
    84313588918715502509430458520458191523500070359121220412486652144567279742508088694542925832009648339167835561413635479164248862785297467,
    112836257749136569307861063497965566614534152780040643766281288570603825074245840523172766655277851405867349579940032775969952046310212989091893,
    318590856988800146866354876940147757787398036078985567662384778641031906013826202976602156381664147333017313509556839406306481446445622755345,
    70168181936219028588272551519905082036346121198400205139036718533680402427093722638852910272424832269359156032874441920269575524600669742845017,
    32748482640774733778501150136628367017897992351479359867970377616881754268431321501475217486265317373410137512627827946856305277523874296843,
    33591552875212879957944849988851028239709040438120870411802269384999428252626909892657884452152187608557806579235401537153246929780818723220480,
    582279302596484567702761069859087500579641823568058678735888756953158866193176018058534728378524525091185305892345246009113603745245148481602667]⟩,
  ⟨119694, 1080, 129, [
    582279302596484567702761069859087500579641823568058678735888756953158866193176018058534728378524525091185305892345246009113603745245148481602667,
    51825958907317462350663921155027623394609337331936779615733649543053786845507509911761276809827456689004856872605860450388510004899120946672777,
    179952798490708047134010733056913293092136369711361724867366649653000081231126422283417580189868560573469946654393995816402032502234785310080083,
    40099032449891152004841630214073551983304717830522496713757020387584995211765743810222312318967386826112452882342135457211028927810071870570509,
    199467836064378843939054930360574075723713774774527644893833228392805262950021495693704197457784505423650890654391286425182390731211385369600,
    551915507371512091217848444088383311275803884746692456012093779650154041818849518709560122187194186041245149026970047667241489507525578457285655,
    485728980399302488333343921489504578798020062780403677958717529104416053647940432734699372141505387626109746365102369601253402213659252359269,
    82389879960828461170414275179125237326621241946526649708480751172501336306828649257085366893665611707371572495671743573900784163693587]⟩,
  ⟨121308, 1081, 141, [
    82389879960828461170414275179125237326621241946526649708480751172501336306828649257085366893665611707371572495671743573900784163693587,
    57961908479594151278642694193235017127398064261311456904289100143936259205016529467111586599529533722573670247440298008361585604333903394434048,
    344522616500885269291126657831236707795957799829301554864181651281880128147993572250921529131898627899985606135505912376551835008159958477832203,
    33534638001772349546820030391722468335304335441805641461822961441899876199589531462803383643908401202462242720544068354540882154245942970166272,
    128048669176015982950477001565894758219033770853286923239482252900616937886675282650914097695731711945263592940967527147673716550396755850240,
    445792668367356958972226041819383659781426111537844405124540810376060709050055510076841842007280319992522225489500894257926047659982997,
    88644087873133343482341620560931631265344211528959308374533141687883648063021742659348696062779316857585876707799208364612030721400097355273233,
    50611509453922337360477508894899305469616465988758104220036042002823213982124479612675923136254820618962225058157465998510402619985701774409,
    31666660576553826686252599703117631691292861655153448864868503710102068769714997545478878680204438259349284862194427559114698556178432]⟩,
  ⟨122939, 1083, 146, [
    31666660576553826686252599703117631691292861655153448864868503710102068769714997545478878680204438259349284862194427559114698556178432,
    39631573565875580958259944884563246733145278737322116543868145570476394841283079471202892377719081109088952463541248990291147157831984364932109,
    94506060176705679718597239549183010031976150182108578513839636404623926917391128245323842349805220977070479223901452779625101242375581796942848,
    51882469164354685305348780797356379763502102219700668770654047237915952043650406415021135534931331903835037167040497642631427258793783525942621,
    241171776198423822785983959251807594409568422325873494265657958870074114614505223185601523567576915544272258073507618955300175872,
    70150197413213396686580417609116970624447997008927026437696036895640169366966943407453248868928548790479670521219854057585762288697802771922955,
    33573544293108757663443633293343582090856501144380445080067711000377838161851961922015090145225700695905828270593063091618239911601512753671359,
    31981217181377570197380144603848388378123233143506407331653329092479745378784021941665278163587676426180293715715550260589853942359261213,
    84514990040358062125452210080355935783383519442644114299932570097600329127659210300887233710010986523380132684251975281073880758894985259]⟩,
  ⟨124596, 1084, 142, [
    84514990040358062125452210080355935783383519442644114299932570097600329127659210300887233710010986523380132684251975281073880758894985259,
    66906236102523977748529422539454430786186797513723873490035834536781541637320378886473125436790440140792215316530545920964259113530831981,
    111058989533273168970643633151780628685980558903831514727085586655349499442322645248153341233706001909314226832354542744221635309129706810499,
    546699573109607969980516541159235765373383713986968397119681605693863491559663691176632560191614054366756912557700242573450467265117238931226643,
    58604832020949584727781953254028207911383574496655676531732140016461322993612385547964185156051602799542728675967268960116905958043685833670693,
    241412609375855016015920810815083086562130613369991571350504886169333250854883952299477374017196648802645843359216703115358494633917693054418967,
    39632146141598240063219934547919038434213327798354889126782120005118339527385725603103935426493604343616224470281401581687863384662154298785805,
    711653609914442154622737114019092007047439650054117764701538971281564445245573665513317177961934417865365893429046934196992597517149794309137,
    32856559982888891193039552726409454506659704029850380817271081540503155216815513476109266590950922192505057991913501309262447905530586333195]⟩,
  ⟨126286, 1085, 145, [
    32856559982888891193039552726409454506659704029850380817271081540503155216815513476109266590950922192505057991913501309262447905530586333195,
    33841346482925870670111895640612970803060350764633051804654900357923261010345027242422606130649037943556518234342177984702561213074165930667087,
    783485752193871850682549678354191586324134589281968182138537323653558255175606331911081868363082880966587607618690469152636778172153642261443584,
    862787764434488439333277636731326081896464187743961398653992572526232640658109762052792582361616807392048032756219204241661610117788328688370735,
    52418391486804151584260691768965003000057951069301481979555731497714852178906617130831559131342664827383640919380377120622443530628882705173504,
    217330676091135907479948766506177886594263547869657549676513149082522352841333988512603545920752958716877760851866274177549849434688312049695,
    496975573646169518166337658209134678187498250063980284243953646738050365539501665781713028976755557870796532090199323071633301615252516125029376,
    185963818852685727916040325952961315095529805793890548837774123419772495090429806408948449794040035590990541335094156280728743973000698323271680,
    509360446231152153708712967924466184267266231729765279280957983879963431852950420646743165694772054709223133236360519129920367356812072478426112]⟩,
  ⟨128009, 1086, 142, [
    509360446231152153708712967924466184267266231729765279280957983879963431852950420646743165694772054709223133236360519129920367356812072478426112,
    424131226824324967928950396139912163191593933487773934157485009365462774897262863370511445304432648922327887738443842513185709481869624517614592,
    157787965065916550423523462271974085422665815333114846994409985912852950380043936920937333075597207700409762906204511308003396763940732010496,
    39664321838245517840471934938685409108225306931352326647062332020533768110092505811119051949380668748736324322708212239477216298745849933987851,
    33534408309292664185893154464803845793358057195798013573949687797405547797137631186264469327992167402959525502226571165953642167964044046117888,
    125578412185635125576507060280170918210636439840290666835683753044669646681204333165717698880092528149780947146123167207003614295147926376153088,
    125016313259851505424876679540057383801512235600898273161692517138476922491004266354664774660810892712827812331538332671206585634372190227,
    58045131192891428769449619066806686531033821101689235448592404442662636311488396570687756117535775718039279644099824089883463479300776042430464,
    38770569169315964353653888085609567273755257539489149848212423573386193577033863998670112707822413609581786534108226618516302087087063120913]⟩,
  ⟨129759, 1088, 156, [
    38770569169315964353653888085609567273755257539489149848212423573386193577033863998670112707822413609581786534108226618516302087087063120913,
    94556708689601963003458254988427720357690040499969448856333332055947213228879191572435349910577035569691017390559464841470716037557030966263861,
    311135304455433075256718993146932050557234426583081871828039931796405565224378000633052763294883322942788535260926030815198575383131717632,
    332584281768975427820727137917920854193668028849379876586894501898661823579011953792273370997849990936350053845491549967735350977983122112525312,
    92956858164029460328914130366212773570652127966258095977127861606404522226504134267638569561869447830350978247301752856397331678710062924823,
    52090953423655597538051449009279957956155738056856241127357274443947319234566297746072541604430615295191780786822314610235468346254824615968768,
    844490120565661245880893225360384736703574968446311505517026228369505282011096347047361328994587131339742817299491426836807427723127072503157771,
    33602931703898048362847215922342747922339896580645353343874619105495771438669057359097267831754401961509079555945282320126469682051898196110336,
    39631605373634499566705233569410629428904619396555226245296057023338468543334347155773529022863427577216974236332716686333955272518813212475405]⟩,
  ⟨131537, 1089, 147, [
    39631605373634499566705233569410629428904619396555226245296057023338468543334347155773529022863427577216974236332716686333955272518813212475405,
    131145787548842761772904037161177440052385500146283700444683011338771333394346598293670653234205947443916174659966178285441301410816569834056937,
    301303724850853283723027025037690510300324074058918395961833024309509277789496731002211641893832574213507735665814863863085731940722335095869,
    55475677891661964885169637798928441643764806802726143767464174134010199663490193543865109887983133365577442590603159675537884611097919488,
    628555623397036987452384149730304231167261367827189666402370175065865622024793426494336385602795876990989582264333167845661161518979233129472,
    38703438069230567540003578290085575718418895859627904295834464308544166542378123765550954354605057460374734768449469135821028318523955347456,
    180708937537418261614709648218534932953198593018705393574219733144453408062024023454956476625015806493383218146445148478605417546578040465653801,
    110918550628229222323102024611559206143729522817604978192126689820629515295450918250616674687525810825764410505628529897238745370954120066048,
    143283380764303953651121350433325803286042593806032330049331878541282716408522918719045699822743898330792699539236822973757247914149495033574400,
    1076182485804574119840318836158196825001164805476450050453652310765419144740785566460888143427805767794172666796865454440374401039934095541435403]⟩,
  ⟨133356, 1090, 159, [
    1076182485804574119840318836158196825001164805476450050453652310765419144740785566460888143427805767794172666796865454440374401039934095541435403,
    33585493470583194462783082361212723174911196427588487677591913983447962294145643720899147333936963566224596384878455675004994701771960359070720,
    70918279459091927876400039758357314583207826843528797449156162055699701500730151298861476824029982575172463687571170592852444990539794349031467,
    782985562566348760436340360296188145512866372740858923279837842048759522242717928222745691288873882611563952082397475441572532589653030661151,
    39631681098257789404753379425760535187863739470469316418853734646013259510503462747245748215275249172555377900008690631558258992285637408736269,
    51825904039292343261314245179429799972994398887370850942442853925817916977944686601341311846989420381500908220216756469490800903642039562888192,
    181671916691669226107331717459838105648662052875359981628959363286183480025767561853180062285113300243169927089438888775543853390056255728640,
    88608412399762108121193138193954229112397487472640623162546768573906745973713504290120767644977094182020548989697596246046439149302198033225011,
    139925605243374024085710393286727630058077744946390176157258391274241252313497931004571609301088935727741620491127317273874345092564455046355,
    38944018847869809482244695804685568929265876977584348549284872188800282967760681263899908902690140177155105819708006702365313778134442593280]⟩,
  ⟨135207, 1091, 146, [
    38944018847869809482244695804685568929265876977584348549284872188800282967760681263899908902690140177155105819708006702365313778134442593280,
    538898749554089152997938680978691238308460092214232667041829807950063543568215349231228342856955558818273350532484248743611692989479298007063,
    32748445864346582871366425862603909362103526728487187709497297157545717726044512648603098725403411217758429708493729004821270605907817922571,
    33858915616461295385549795169755390460210822227448469033795554420612930064891137007155081892538791864951732567270470302483514166219113840520192,
    68506176670618758109802532727074076220281773425817633390678982176712595980725680632431598616721642218299661926047404613910777267372948524032,
    836573927534860436609309352912578421166004103684949340484283285921539000444796289438469152331397365186428968764364046270964036983006034134016,
    94842475544323466219112957600698416053769746007188485237102545187418796011590146964077726260699554793799168375775145740065866620761050444831971,
    105269950612501563744548258238945758455157983755523032080721308152169037785559287888830574715281466439913904227859797605986765338911773,
    40438460350594639504918686409799930205747302174975843344394973622389987349618731172642152408289641076391064158492371840442342364229183580752909]⟩,
  ⟨137094, 1093, 172, [
    40438460350594639504918686409799930205747302174975843344394973622389987349618731172642152408289641076391064158492371840442342364229183580752909,
    51096762317981193985337730123010618803436473971072080975599166796686157662096565357812147442467807810492065882227926507943566954864055634944,
    893234692668009754356108368546130745192932619269856636448592257125425966412165735256947335454996487183781677363423649359152902999938554860142611,
    57923368469508322901349015496495163296150296104494185884962373388102010767382499722507595227715022360956903431515361015050925500963777019904000,
    124991885608820814145349539432227309872016373309706578129683634324619141133327451183802818842765725684410112129764783111034242979205748945339475,
    51858652112997726494681665881968193557641436102422798502394151250508497825552879822052163765815061542605901813676333503791821346838969124412427,
    33656508438964572993528988876073245258839480488134517417316473834850992853658436253354071128641005317261079823361145360882078855378254973381705,
    663932286385414485139567195968210146985052100931470326831087408964343881438920701425542791203206301727160095325193250734416667195050510254080,
    70203965608383628863578521941513823254241279636761588783909654412339814455283323944437207334425519364592559941515710727079281415826558101238784,
    734708399137030764241012891424167696578180124510367167379419957415270819762243817715727595526982780822139060395707934155537458294521627598279949]⟩,
  ⟨139006, 1094, 162, [
    734708399137030764241012891424167696578180124510367167379419957415270819762243817715727595526982780822139060395707934155537458294521627598279949,
    568891005275662761936852313542599022381007790350122355549791576470750066008931997223995419045375247176160379150726665170576030731697347654656,
    802012408972897774167575410763813699945445562176247975499591054358042120268719157002173009394352258774762554956327132803127677103173533662465024,
    1058272039464092370169291304231790879196979405062904419063039612105632714010823867131042248448896900212211257340244780365649712882038358064389187,
    39688138971930775039558630934930265660858923093950957248400288627693396026406595856157079038258606933463630809978340847961815417596471084580877,
    693761747694133849542299047818259410747616012187907289876516411007668623157217481941762216449584773907476675737692850811437214753182871223577,
    211431570188282574769324471137430566252843816111369663731483908069476684210641280901743202915953874554215005112475763730947644201455963865088,
    32748840212576446440894186747606153684943731665301090539582487884890975662006027506219654694436279502067390757744932792693948244423572717579,
    33534408255477918420741065696264900208901759908288745076898532547628036484044442249576816991112768023281590293154192936642064033439029312629777,
    131127785792466471933339838912792576027786821209663386276896330060969797446196185332066882620810942855477526577916920685870594885127638254354559]⟩,
  ⟨140957, 1095, 168, [
    131127785792466471933339838912792576027786821209663386276896330060969797446196185332066882620810942855477526577916920685870594885127638254354559,
    88477406357992306291050113073262968636143043164603149306053332349684419498270126599742385095858581184817609143319474481391790847850277582709760,
    194793074833198787243374920727962028917924983136532209972802804289998232731549454278752853410411991022024649700677384901175152514912223269,
    223472552065380096855016933474388178276863156513524159071364426665999448696616920676496758831534556750626940247167271086891686004200564711240723,
    52144773661681013027308693945826288801273911535470602311785120369799236540271908579079285993292663580220589438693468988776914295449011638763879,
    675808831259548025010864678141624021917557877919510714619630438818459456343696606047546828141120654461271655614533613293643375067330503507968,
    460336017293925922717606627669777468259084296654940946100213356885134034221271661859879341920832670527277053303685496815370203496021147165785088,
    112973205794229923483230903305696705954248172596249912229995850169745234478933435349397848511855312110844720080440593631907381348626588238926848,
    39632355471150837306810000265531335437892971262473262697438443028103986273301921236651594814051978674210900794437545299223646290293026578347021,
    32748445562103882466937020276848927363914846325576019075375032743443290733175358342805372020537375702906532725930331041119421121179841238027,
    33751739271664635184123214808551256766674574770901033583064154579138201353426115357886952324775343653369229605628971685274873846540031352646685]⟩,
  ⟨142936, 1096, 164, [
    33751739271664635184123214808551256766674574770901033583064154579138201353426115357886952324775343653369229605628971685274873846540031352646685,
    94506092322253320535889209795017291883247224373025796101761716168354693036699071608725088097622322526749231438736983098211115050369689010044928,
    892833737153392195287368657517323280057445129275689891876362881542548012524964767421455827186803254560736028996667050756010345798424349775,
    70156221758732761699102814072428372357498627044655659948800962318330635903865150858543257475276912709659992308463541020675344987983111613579323,
    56603414579436653920354161222977038667717135379522580725297004648594479175453624807341378271419676343326602511922433266431834290375990706405,
    31231463261498050226178252750547411137229441170618663793224319985857242777957363155542100198586271572344260172982652571652444751134720,
    527404839656290514163543308436994826095807872124456037262541698468446660947811479142110335980277990907710027999863523290377755158641702170801169,
    50678103243286359308273424682217689135032154178977747868282169259664477150943843717231643814396020788615546504130998970912668791268116004864,
    48463674998478680199055136561736561774410839374698177752036069276735178142837196329578793638599059447474964205534618757193575225622528,
    253119129021120787085384964267481072270484963275924054362154835825342459294135862066981089855683951640565212984251237052440572831345137094230077]⟩,
  ⟨144953, 1098, 160, [
    253119129021120787085384964267481072270484963275924054362154835825342459294135862066981089855683951640565212984251237052440572831345137094230077,
    600603720949539741234383454717101393196713180680079481787526506407034486986597218912107509446693514971324898569679671188984550866985593831703563,
    33534911227913947994390283832345062648059483622595033842530941070977504699781230388572511083662624250486992389035956527988622855566518974950413,
    728611265980614894602041207703865362159204795165529820902183113240117031515660510560611465690581511827644939003726470380280300480086843024669715,
    58170220137145843090381629044773438599686523879455589012352864170728911095881625104547718264879139800375249475596519667250306900849147873591675,
    216518659261783920388105240755207172085992489760566849635916517411838816649478436669897019862328717174961447732874529943898541015875119050136673,
    271324374842870702436959991571376560158895433978575432122476792481673285554228290654631069176169885292535359462084321784763817956811476989640704,
    38914976530189673560515537772817648991351443852267032663480264747418074226833953883765130441041419282055533144332541714810398638403730242560,
    125435516256796116759340030431800702455372625008848482878442551667871285054777198546994997896841299613934262686545161395913562096982526258084864,
    30562376664701586854522906440561496551223927632303149376279486338415928460604510444646507932004176842122829539649498891146427891969,
    123146868289813731298691101995945577213346414964540718086822062079659165386219701146199285519159917362276809778996654698936168137157281592367]⟩,
  ⟨147023, 1099, 174, [
    123146868289813731298691101995945577213346414964540718086822062079659165386219701146199285519159917362276809778996654698936168137157281592367,
    89394324989677603173023953486953942574660912121639563743956236928039029705083983673322840208329256168336941418858057918814351892764614710001695,
    820101459417244030479187314835740049407834743525984077878013776028484233382503032213033660159669779245092038694755099766962582251923524702718987,
    33716138287905784632452752170368354823731358791123730571347897917970852057811342569354421058922593622772799642523491448087195539570665602427904,
    56597477783648869585928302386737235538596207895618263463353965626373459813345670719309187792445079133008406982821138061104877704963671743505,
    39682478437092732902106688545153643851755111972811699691957184608510292328476658081598563329641227905770429781727509435767365665596599720709133,
    55288095633296429027544748639051306923419890651104925723202017872431729010721687539764131547559523162788270447190983361207973521062683648,
    70424325628817116428046251810325324471105536194839579930265260137321952485978753575351918326615566606499531489974009142273969034580741410783429,
    698235562119417842020170134569045988354573448298126280083097907411479609133144262789770197691351355189838233568580801703775319015549878360097792,
    51825903667640924786499029108841386945433757510459473350015976462900814518408187068819188040211157859624235354750839181679591540784917531066549,
    38702762367132442882332439909662813883710173486350280664846830674698683148389211025815079407956562202720989149122414655195046492419625320477]⟩,
  ⟨149135, 1100, 180, [
    38702762367132442882332439909662813883710173486350280664846830674698683148389211025815079407956562202720989149122414655195046492419625320477,
    38428758333363463076762335815185828201026042196666666739630403154956394976077426540772000910251195056361329487585594617625462525976903680,
    128016650879872212647789865469364726944441184315086157406603534117459865661521354440327820388794752414494899302707651657031455316196082445331,
    57955817287226818848397190638964415091462564449408161671227297526506338468583850626311624914494406620456108920391734992774734339851064959841291,
    34478266994198700738148122255330992864954674870344750945827126878534328627199247352328581038707557251480495733223371654408711728151488593144995,
    112797587021766117931400571266995997038208249643654702811225280341806558092482426799953552600117473856819454299612917682553325835557069891043351,
    92291224414931449791051691702601799440954922552350669385941950858783291161720847703169641777850859646545610828175811554040997516284999568557,
    478627463281000383421183656493953506981772236632891771391487735865496022067908124494929658941551557771644248784803018043854305344431760754119680,
    39700201505145165785026304260461597956762019793578286387652200975016485088095931434819986148199528690107692039926238358214117880284609853259789,
    86336842377305634686032873295346408283568237823265804709536996588677616652713348381797676940663326040234394865227648241061210535473416565760,
    515043800981967759470838255970287524122140589625233001309793647845381864896952458122318626943606860573146634357113324420111869605747881934848]⟩,
  ⟨151274, 1102, 187, [
    515043800981967759470838255970287524122140589625233001309793647845381864896952458122318626943606860573146634357113324420111869605747881934848,
    914115990028112328603800874284942657652543914847155136449904331606555147493442630844968848323460954654995384711229309436568684867473104718865,
    50611234050214026032366509222539307237337226329766393504568118832701540438963125319594230650711195979551918463510416513878971309244012298240,
    39612758741278024784004482644017321447796190842658893226001138459961253875207792040052378820195129899184511092647875106221781010274577425408,
    161607662462914713227051481542936933463545555626417616865923599784426158859073261877699545175707075169186906707004159016113867091164528807887883,
    34281723480597193139827917987851229275418482272003775460132739075935440178848216179284086071349261885992578000686703865629515246773747279997952,
    51825935685169396738461399882279654517053393259950558464386747933632412964403086726926249812525562279394466764848552902617633947912459255821365,
    303832029382980296576282614011379307071038464402886968695534562959998496403090817128382371173767661262286932225363439390834613601459200,
    49547737749414585246760966163106290511584907763482642506953664622359928383638539454432120159594763136165077050524394265844426360382029955,
    143283470909388219491331061296561218658965536749743516155128233197871296562148954038637582349188984518099490687943638945329701896321820047473664,
    70418089383480780843523857894084805145152936820625384527030835339250986560456218722033519867359401656551561036394695415651503911505891384452096]⟩,
  ⟨153449, 1103, 189, [
    70418089383480780843523857894084805145152936820625384527030835339250986560456218722033519867359401656551561036394695415651503911505891384452096,
    39631573392736175878280413068611064035120287044564218999876893566235301389026376723040063100848395425137034522713574939696645967417334879540237,
    58390478436832069959285539957090056500498935351142344830806764497959482044436610666760109590039276645513017956555195539744000564434816214237215,
    191006442746057114985502551653277448011638349083150829614142561915479415394898873815024064415417638119916972376393458905207425404502165,
    66985570916878367113516743550269416912801619583204250294702895291516687211457606959147714108653939014024698732004282784418039803376172032,
    33204900280772778849643366538172619244772457472125243095870442464882975512107155916244457248268850453474515905406366659104495062779308387339,
    33573111795692300127711337172797990185951534906146163901321550949038653037381701137776000712768927189224202036546343910058465462892102287371264,
    175682936042172753089898977357628369449689890821978571841952112826956552341827346700373459790158088541253728974448163228480393778225157767168,
    139925176491596585009757266164595443644759475651444927512069200116382257798827897120911452256742176204637980993096881425144171369997999848465,
    125042496586346338368941278498658558368006500311074073917548556249486109224377619276233877083368167645062396730539034723109728994830626096952349,
    84361594697113708772396209776391977297363305743518466041237638451861706088231301340844812150827547646546329893892301734627979123543264339]⟩,
  ⟨155661, 1104, 183, [
    84361594697113708772396209776391977297363305743518466041237638451861706088231301340844812150827547646546329893892301734627979123543264339,
    69291020495946311556969006773064963895907380236153357876172261920238656197617227369792440785231986360964359671479973921932992322097383473152,
    56998692759296721524635484527943525310848740142780082821522370671505885533729988785697753081239290243800565441968220369327078681864614987099,
    52061097114450845501407397305023761094543026408961628750029841499875125861908911224481191420930643449598553880247650513485257383983535860219963,
    39631628632861950917444920153256335970166767184789738799710775953655679263801539862014767477082389770600372906341497137640185515387737507769357,
    387280189508289237408357145670328096686718282174384444428126339685084834864979442744214036313063829161567063278452691985618000385815057334963200,
    32873461869577809864058970923116856636065567659568446712062832985621839038862721525081638102160698629165728400687572740608183071998920884235,
    33627726309963116399616249298771399421882763518861278763197296354464373373766768012990045589205881514094219443324924413125682776325703588654117,
    948195547701611581780070482391604381054028349623480327100513173197096637546353543090406361255971545106080495978002863541116691422072793700761600,
    38702708391292476356148002694761406624639931944681467050322034565287902314490101654719187992315025371710255603728695336692080867705777815552,
    37795666769202330593668970442386442994784708351944809677085395166210553381684488149712633038781410404661401248709763306319002913787108371,
    57923177362029635147675551989014615164320646047498452679823669447620848510952044184417783721953073192620397271093084338279245649531208006107197]⟩,
  ⟨157906, 1106, 186, [
    57923177362029635147675551989014615164320646047498452679823669447620848510952044184417783721953073192620397271093084338279245649531208006107197,
    112797813826531763912289863376851216781406660066932045025242145893386965410750266186131301132298375670623259979833691187016407382544158445024256,
    70117399161736350731349851544656036892629933577978798389261401128152754714006774399485001366768766546468448915841325836949661634350059785027921,
    308124170911764290615593474336755974720538945526868261808032201760997796864573653580307082249777962705912009577493939493760754066068772363473920,
    129130255774019490282770662029076362777084614253311089735105965663621122921801519827112663168912721058447410987410895347438634605129088730129,
    314055276063474804802737544630430372789204185539076584932477309947779868638718956131084528381139279831043001201352771915545527824446409996763177,
    39664388755674627220111594266352607140962832163726410374227555384705118737939911042174317157247100719887154857743040860090840261210615036570635,
    33534408255347602616957141847448481367900731328846208805029331086816141695583947133037268506624059134443903133786509237353176706456249846213632,
    88408926472338514194952612235376892370476154869117397016668819616604504914912378500200891848884957846656955521394307673488702821155809353810944,
    52358900611227351206203479371401636576405635335504994296766253163597312944674797007248374107008705444032256300436766625935860717961065785228527,
    204311598361381482634532095194767169047881698650036548333055624921351875194157236248750625558311957042153647692511690547930609077514883598123031]⟩,
  ⟨160199, 1107, 187, [
    204311598361381482634532095194767169047881698650036548333055624921351875194157236248750625558311957042153647692511690547930609077514883598123031,
    38752133544373285519442828808076627508552585183005144276962273271555947511073226112459408430075941962553196176060856525642727460614864633935,
    582279308442472816426510688540730215869614817956022146891184173979382302024793278613546510317179614686695784456632767668532095333994231026941983,
    1009149304419277513383452536879471755960678476191375701267472954126042883587579867119897713824324773047601012911185588826572936343272245859188736,
    36940768425845490488309351379328087625394030338671541438961166666751547714515504298776994287778843988608828059678076243929112275596288,
    216449481642314131934393617039361902644976012594942290819963817825873787211290275947299409924692878769630112105683872251169705648950567123288064,
    53945062010557587310546244638559624971884089115923796180419739608766039703134750675224185271346975184188708649021294496249832730001451,
    32885650653130454281316161531685215938537724033973379965464165692718802744807578961432797771800832378865413341562121845265660043476521189387,
    33534492719170631236494695501702626681440186574236022718891834081115275382303727643481180911226482790278753943036714927824587637435245707406355,
    39631605373587364192482016880782741619917691531443760760192014184484417767664175546701998564063130865883409043621554254485026633012291105391629,
    154211896265258175651192753733313898277628595502319391993891058725641693888610128184273034993685097202498545583935075840715673968363772928,
    497076747030213230924394340497547801886956102521553279632393184439132218683466701944865493599482832597512481365124637272223661976575195184365585]⟩,
  ⟨162545, 1108, 190, [
    497076747030213230924394340497547801886956102521553279632393184439132218683466701944865493599482832597512481365124637272223661976575195184365585,
    253083362741275481340893173669593580104934975370365970586781635263443333911264806100210788916246059678977426219138938950925337606673830596598784,
    31311758855706516091337299351415667882564287554978120366656998159540963141086925760370417130967196450005766387599250041635436807611392,
    94545457311326325640815663390141649834835310929586536198313374675828135330702734359181830402135729145392643530314543757381941116751732193717248,
    70117436875007269542693037462357245910296703224460343971368177552592952234231575481285952599636215063137946298413343387308806248748342360163328,
    51912240478745416437646217630218673719656608394381570245928570165998500779724638981768829726669254854474792713448153872743021445752859015592960,
    509205908609418999029370049211365930299753466491832660718770759825368239360951641421771183542401716917431799723119334986782236799176480511767552,
    295745307031423682300092585494807701291570018541049850925460732924469684783185725461937765808725929264795471709076335344757946339034217979081739,
    33591040896840689851498624644370213001565250408224500978498979371964837071661345672974329435463394805578871013201706150850111016096896801320037,
    32114826623102390226462127600635966161566570754478678703729871334157639221613648952218264425918610245829321124313052662171509476022026240,
    826276085293506213982929248092403528919269005019611188015169536967160385484979305669664138425338171436765742236607346858710817964667387337970911,
    39631573393601249224984999927923649313662674107617020931045349345003379727057552759080121590634670820526505996051662175721283894186704503901197,
    317903926252592293264050307102108002829830843444539958557026561677124349662360530015173938891297759364760350898654187294725051199770383383]⟩,
  ⟨164930, 1110, 201, [
    317903926252592293264050307102108002829830843444539958557026561677124349662360530015173938891297759364760350898654187294725051199770383383,
    271463773819523620068589944238928941049173785518702001323630230713518335706876706660273537874557281034621991944846523007878831417561359030729728,
    497881672732655135559246196983656955489690446977713945984060128799910695879860690296837441653795611636420120208067749130012514320444263759979,
    606736405187493289952690734984620258354180705610411253651287052224462928348432675264127158389933241359277711037064285578437243032700002145140736,
    88447704771946042690043645105511639010652162781987163190546387255799710153373120635323693838400486883307730866984813069868208682897125293536275,
    57923106665607380943573923331224381514297063969304009868406671754784862213950310992541007665448825956590379490653029941619210500799520964608017,
    1222514358481414289410955599298233387671912485595217481090913200579063274459041484001625554427232518673934938762223513227741143738164615016611851,
    33534498420259194206264741115264648027613917063306020271086952256604892822941770444726046664396478255378716847347869556536430345362939559554048,
    31980939959820262541965523606253111922406230916853770485629115721408867164718473876629311554239853055139380630155900340414802782549180513,
    186538123051785588540149121431615942775281214932161805414532990693044200689826079161388393448562848792764101555355937284008745689781499007616000,
    51825904209645204433740791883020139252518646658882520161842366192281300241965636382950186968322291709050443474841874527638779281955840460035103,
    428721278993216882531450133319143033321046176915777677811748917830921471963420425410683959132504762853338495336957475737458052474905953]⟩,
  ⟨167362, 1111, 200, [
    428721278993216882531450133319143033321046176915777677811748917830921471963420425410683959132504762853338495336957475737458052474905953,
    39807273603128848710746397325109894643687007763912398928439230718018450757433524670424240165152315085649977787835604535185612975879092366760973,
    979778647485891974977024517232993839118406722922829910793885560736877463985677969234435254077910762539081204870483393818233312348266843165,
    679962013777110593808992929865114226993564587706184790514175623721798893947622609114323152072262954382405703039006507136282956646352295249912959,
    70173964576328640928580256666300043284570073179714483227051856574596795599128521742650307559029614627222429311827059708495868827057411638427715,
    131089524456735990852140732294453111466426319812325252552698169667040817244948331355131685155588331021475202966375836530119848283278326491245568,
    32803685304909803500379151320361682158937651074947901167890656801468484798515058205189554333534751454462402120346849708560164758531549195275,
    33799410954879336877489614771999877570008739048354990269910958075845393227058664484175538641965809071778781584081992441294978351915582169820219,
    407898984800998291278926666510864146681513766298119904916271197181680500957155229099986989300477656568364122404731499761031454142037505343729,
    414103316980377767977444226144948566036064575092712772944632166461370640108298711608772115114370821857537084039198434592326416648668393255936,
    171587921115245693122465398580489955591065972590948113726596252926609665588688012961548474563138488957606207270858113706021174004455513161,
    94592690403512077531729981991807426349056234034078924668170861976356869594753925915126771082695332255656179813278065893654800767562887526183953]⟩,
  ⟨169847, 1112, 195, [
    94592690403512077531729981991807426349056234034078924668170861976356869594753925915126771082695332255656179813278065893654800767562887526183953,
    344540560726364615370623895081276602509120169279789709302193463848414157456597581878499315204658699282093300426714456365743219620405496737955859,
    57923068852958240046081927588706651198034478129975490920218063889458975067022886670143741703764704439398867971945815453297395933925196834042983,
    39723864957754181155730862760250369989218275880524683868418503613560367786741077758799676244718103934107298617203834270490302988072079745613837,
    179934845574167485255932760286595184541129852387342935981323444832101396550426485338431389686098354905735510833100521566937214433209616567387179,
    51826145060279372078572449286093034223916260427091784088266426584848098062541641168973165262200993115995432922862934301919651408481690441634816,
    32748511149740846738094445629871868946756294609171625440122081031349280937261381177072866996306804538531284696288368800415733179138598546443,
    34120952794489400143794419823711974283392824203707045959264127054584049185159130672914090634011140854890312006144429570426204001258988663483392,
    38734811428551572950399291000729910923140744051927007607588480738035429260985005722217711706885676642211757222455821059313680102393845383277,
    37795613888715041720186656259536846821321160508470465322877220012794940383254975800949490076729019862719165341581781080865546904273196103,
    417944593771808526637321343811910233717903977073783857289527474161644646579699894058281589309722074053572900686427000263357739247993380628614337,
    89549135860116423389149005816510377856398408918407346304632771010072054337219704875399312458223741292824825063213029721687590982442104567903232,
    57312718355653675497488393125470344393856342781466644963596230368172181964108898066070675912157775419070539810737106827994310036318318493696]⟩,
  ⟨172381, 1114, 216, [
    57312718355653675497488393125470344393856342781466644963596230368172181964108898066070675912157775419070539810737106827994310036318318493696,
    110384346878964762366803032980800144080046129928832817179051802263143183069763703736579679993646767253895893679131252822820634843294192393216,
    222546582752534746089423008670293929285715165847493891055159302755532671765409132248323678608480112955660501020399978955941143950006944116244480,
    124992370843801188737704420470106913931276609182143898752662377382271483318765216714155517124637249097188724484563894295998657572867222132675621,
    39866857052926107080157673222324857703478045849901707611811828111735582329655644274922426494080202872435947936821933002693881390897022073076749,
    143316129340469831236619418804089170700645990372764997556895507408875522981347223353311716879522155842138299087990506876632843427973345397702667,
    33585173633152367077025484912790363724808355315145986010522138235718177069006347738733116327911349934911083418689384711919434055362934307040455,
    1064113136459268917928933259535031133241144328660398524145476169726846363865019868740495872688024487424355178017594732949621634584906336051396639,
    112797621909929924998640163299921730389766677912454418763176718778915441054217349380977193160253353829427136927937717627161835690334315047445523,
    57961855826374572916878210475261909812252033905608971417425719529683785995195608185760743237025960750737748207658307041822346456734186717856768,
    52507704690446550118475606005521899431890778413432364358302702976435210087061390058923388913345664017923444994854484864182270275743578788500763,
    1218324193541202705524786336060100239326239311257454187216050897161897110056644346075430063352769344629292578821170688413670669368335962997029,
    161574925601430976968909935116325082370544956784986723835324351521513833550790200932768957930545532936339914899813740836197579787934962395657239]⟩,
  ⟨174961, 1115, 214, [
    161574925601430976968909935116325082370544956784986723835324351521513833550790200932768957930545532936339914899813740836197579787934962395657239,
    300690272916695037759976694844371374790512456478084816818881524281661991045193215642175948071042124480091314792700620650291475708838965936128,
    140050366024621912819262955298412298664570275694739422299901637327811328639489917840803741884639881990009627385938656803984992730785037466677,
    68680444736175768225136181665920340634232567211270907139651480864114007230806834699999683837041480242306130985402856270581345033316438691217,
    33304054728973368196708265201592277800892725277692450483280221430208845535306541128056214753769056108729409369416305020793560306531069725707,
    33621056219346187200376307314280848808984473359129595457701514239165498109625284983375603429166035810548381240523618965791139035992000009612301,
    32579977973831828667819583096615740217714743216965149932304016909927042960713272416195347400235910807112978750009723737254035015883334745,
    94562625230637349025510806617087097073875974878918976217104009483911506486689330691863246193999239128979903414374836499784675139859974566474752,
    326198335156946145069107203638429042880361934952488483056199694079972384980990819562477856628087691072145942012680084087354875896507168919126057,
    56366911077107878927390442310668902994918576537954005079338080913411932173313546182295414179301313134091267464657446027159653902309130240,
    332334816176313716219871664490479676435514181049544305546128266468597794806037911250519309007062499443351108934778901582741842170759815485194257,
    1155463442554935038153570811468138860341813445237064139301131077316630707185912808601613959668779383682183540016570873541051804032309183936263215,
    628174776801957430763955709573302576167479795693112836431326817251194170375254559770292173466427061680391589297956253598869027824730939350016,
    131089262726642238231841015375541926541645247891118135666597278860798672608331435359694533139859351460411251794747870509142231819806815041893376]⟩,
  ⟨177578, 1117, 215, [
    131089262726642238231841015375541926541645247891118135666597278860798672608331435359694533139859351460411251794747870509142231819806815041893376,
    200255697999073179545879607770779883195897597424074976832128185288690249979528224495883458292673054931656060601349277046194149858414739604480,
    51859666779829079237195082856475503894952263171204000004638760105782916294497931156262687426068233022923570615253564934212664672034020081532939,
    33534408255849455910999893736186070000602334362923940340464021747487361452713347035586438053714526284854306101191181154969591826632368873024931,
    443624561696860413792685992658735586500198816100846304389004509793518146940529589705180081646141336014257320359819324726068051481890501165193,
    39631692682297347727895977102155431454039704623423365307966248473153361050756824701365130766845234060013974437204882459907101269908200179630093,
    1277356163141684446204108381462459216069672216644879280872407766255145673435476378345207120765370521851777145750520844488463151697607919227895808,
    388972397140632112188508090446367068644082548294478596639131747805693719821857077821554038695728382317205916121658226572808971551312896,
    31295122837541680189444403668771003688086599309558779527832901196341915522586865267131220812336682915084272027083477430920714321640448,
    643251587773211260295441003696315576665525691579525157009378467773557081413351523447169464977482815689164497634971015089664764792131370913727639,
    38792836423604497597760283478070774492103374329701422814969119435425036322461957780560858753013385937316530860393207434029457011653874842647,
    186532206584569822254885641005657002790123218907062105203467709282916319853895276405753861022190951024392388897401727046673383650193075734597029,
    308082491328424733489482880097989100644614814665142631963402167872588924126648894606879708452748570847339912453812544688155967796085254595324957]⟩,
  ⟨180251, 1118, 233, [
    308082491328424733489482880097989100644614814665142631963402167872588924126648894606879708452748570847339912453812544688155967796085254595324957,
    253065185996016912848279741278278437257273505794636821018427412970721829237973683624841935557251367232651439715148140827540773487256158507906059,
    33534408371791412422054092877852684923654380323526530883047142890795021380472816463600541457749185229703063301920551366388881764365073293257745,
    50643280386493801251112355388126098733101095993802568612510023415627358743227480750870586043431104271333068983144470577975890264794454818853,
    314004004621066669909617668756063936343252655934646652689470667890471658991788546587129494796473682168951641008793531533246763678261039971958915,
    527651886286978656192860473092760077772244027991170754394733435568915411042462933332685538594359223836753097768936067962951933558267423077049344,
    39631573392763902591043096759164163487842156932749434997715452364922819547705853085406934530171045063812614938598164797463662483042458236109837,
    51826011270717886997567817232163745845562005168959649318896195613752949349792256863999660594431036795636286654313307848935081632556147210715136,
    113955659453477640520813955147800375456526703757016154603941359881064393989450466187985141352077763536852846722058662481253677699218189530275087,
    86386236090480918762061787753066044355924870843878269869687841232709614819415189470776361963382795523707338705028055955652088225461454241811,
    57923571777135610555556842390379753875908331269450540996686411519123240400377773117167283164285336091231554652766754528489764104548107105099161,
    38702708391292748063062374840836524848578206584000083266086342252584626652304933230968002757873282113632071307858769921789650809520181507139,
    32786431403544609291344361127330088612649762168363960001844595720745115940434840986929696216161788734212834324303479919980059302099430670347,
    33534586504027094779938910424797138192373620313861617139573397182987502530499513355523852406823439775769220990659985953720431778287652367772672]⟩,
  ⟨182967, 1119, 220, [
    33534586504027094779938910424797138192373620313861617139573397182987502530499513355523852406823439775769220990659985953720431778287652367772672,
    181113821632236600060947175266130465146539105651524443350525284406273703615419330431442545461668853649965626425319566725211525307525642803229696,
    143283380727431159730116058424356999216752492183607065283209991739288527023523753926241422496380365430152385855185170842855580335503167332732217,
    93212705358693708611138305209508139373511621516229987312861258904808573807679205007660663186078801361234077771453534270753311466353121633280,
    387170053089993738154983219452474368711911782860266031853156586609804468187240968819722789865590387088446307431881767833578306659356113493819549,
    1183139384575165312033029399883959062163000467509573771012153620689978889976673696707072874465902668054358251756712703887845072065872579808317,
    39631768290576365673381709042857384889080768785558967136935496634213663060263156583660847013508043594992839043167191046224762575541608635601933,
    88459630875155150724245503692126374009111617802265308604922837212132352086216097939744832445663228270960583033707269883829261161295923370847605,
    295712509209910076486862044454043742505984846812821058441571078343401763057423519165754936501794854441618999299932126158023758771865669142052887,
    336471365009601088571430729983730757736296567549047849543374993860684324459254472970629271402262485793576457872375135249417500744118023791779,
    33478191641055698389899585506098902064148572502243967848987750003067005273320899975294989145480924485574223983479087314458463626231987323915,
    33573111051754521905239417009566461919435822697262661078358313197337633097507098607461152324002404173739264976169241253608684621334143259651113,
    966400706248750147128070661439670377837555741960313816417270845849579854004881333378962128446525289380547699968208326367386365913650223726460928,
    211425810208480435815618063006727074485344080972247650625923528990256538273715402915147082658850496304453590454833514938699893334912055378021]⟩,
  ⟨185727, 1121, 229, [
    211425810208480435815618063006727074485344080972247650625923528990256538273715402915147082658850496304453590454833514938699893334912055378021,
    36956914352936369002364308760032813589319100071871066810509614038942773067873181289222126915796644407250428313742627662054701893956757,
    162238776444919450344772480515784671266903540001100859621569548367982244201862819213957241386818590588929039601352560419300759264675373462465555,
    58051175615625736936011836375205637824032289294996233271892429511766847846142365216939480183739922365557686045915569561283962826458534075464733,
    84314453802121729031013507749967724161499753885531922617700926178778736724597885066451205057312125419043073869785988881667708840147157045,
    131270655469050722508409667034853842126238988895891750872946473469078624097068333721127408761084556986332805805313322512412830095602612007075911,
    39632536474164410274868919553164563024201920515424899600862811088863570504464937764154172209862477637668757788794838351571674674970225569431565,
    600960771318978006408132504342233070816780890737186128818249702267743823479908376230790923383982379106691673639424089252713014404076660340055087,
    862781735310042635684329435441024326437034697669109508989698793834459736604861230824149410944403115474811332719457859844895957101558944503282699,
    33534408255428010302759785936049536867324044848809779155676265270621924132711501433921028999215970525621363919508508512553285984151471756684469,
    70382396230444628636934271286509933302096407039730124591449365320325042385836300363145812525693973403133597328736949173252694432417836711280657,
    39159387494090638329787759611389293422234788597177835162457388904395112957896446158097509947880245124147684198395933897977953833986964868096,
    222632902167669326279345117438725605878855025741568930775864664299039503036021860993450682141510658279447158815117427213730857014632102696583275,
    56806807336093482786991786304683684502343734912937889598351685061034612545992297279682818023548328704337624542506553162789806540173043826688]⟩,
  ⟨188543, 1122, 235, [
    56806807336093482786991786304683684502343734912937889598351685061034612545992297279682818023548328704337624542506553162789806540173043826688,
    204255099001147384627137257737765963878112212275544146628477535955287511613437176558224379798239314511841289618977913810163700279836701065491493,
    51825958907134430980029871163114193716716061247643789154942144716849298413232039368693099051892262767857846156090384226486509724405827858595883,
    765199372368887247813338443656241484908133602233064286153952816792023164976673467760520376665115608041213140861816744393943331469860647936,
    49507370486730845249202628507827537820477220977660387384642572855693493039648557141406687145639687258873506425965862825206586635002620928,
    94506167200885127201836346494682121276169242485229655072504135005428765966300768272296890912962814910449422960801738914033085435905266808782871,
    39664970232332656408058241122460145761237025661420986954396197536461509280944681239864999326078914066044305509422500750798329152905885366148107,
    33769883650970408114523101646242175068582518029264728697011478208569842928930005026941114377508382712588258897236547600243798706796825568881664,
    844525877524520232799389398812766261923549116823339961977868475252432650537315231523897524470124047604361505572311991204526290166844081218556947,
    58599886859917927301940010705992731273657914020283556061783552169797381368872445803866795750453394011646172957825928551832274317667989820972032,
    88894373399469003678142784794554120875463693266505073169558374604827900224969218059081582867705886312444260077447832287044747407728035092234437,
    38702708521609059723707942471900140528517967684221159926547224709177371455717220615484465211770214091796366875126664273452117656835591345152,
    37826845066588826039246472287924133419673345366442821127156308387459461662209155076751659422173135776118321140046499871795679985790877779,
    801141993938448579448703220376972915939161706415838009506285854557352665162116715130329978130665039050727737452701281322857874143949303841905]⟩,
  ⟨191414, 1123, 231, [
    801141993938448579448703220376972915939161706415838009506285854557352665162116715130329978130665039050727737452701281322857874143949303841905,
    216450266599738544736200622810136456467111571789878023645789785204012794615024053406976657002831053327734846518572758254838712992694194647610385,
    50747879766523999646969901831606936568162775019121799473215428192573540284539620691601033009661578041129494281257112537605372655601588371456,
    1313939485452546839081950842903968534786373134840112294418287876546857232722362423213614724219487053183101103757305869211822691389214501326815563,
    935947597131676884616606278157502716386538930459630873691853580746412048202805423190903741342286022401093819142223120555995716778074322231118859,
    33534408255699731678687380727006811549268023673916831521496450214549874425361908838271231936462662875558290623035484689548694556439976857316352,
    39688170870697077204986195086434492018551403045140756521947287587656652587275835914102754167380803281548337068389933807316956754829380623080461,
    70293135017761925029341259002267509058657692092558910734342311077486459535409872827913743138657186725065157666504463491757696519813249500184805,
    185963586114065229388929908278462128106301588429903765970201859694543967814666426564003023096374414080704421906135243777126402337709806829206528,
    241680763996589493568044678886290712237807518754918323354754902965536159747282107250430808977053937506489696833758005838531210396261996265734144,
    143283380758728115115284473726735768220077801969836448508567051522699497194072541498954563191362810440484718713181119198793989193167231737990144,
    38770040345855624008437613389104572144295930836154389029931320662655088587017035397943839468030292813377819492683748916500521632562811020319,
    37849589519445105717533132819957639416470323849128794709343887772117380589932587887543504585396225343358112852646551650912631200177717248,
    344489830921080723947481366942282189266868829107057082772537693607401351445200369162439901217620028973265443685293036292828267640313080194497577,
    36962459692462498846695953794880296381845495110933594117326034524088215157883275639196840358965993874436498593553723842091368513025043]⟩,
  ⟨194333, 1125, 250, [
    36962459692462498846695953794880296381845495110933594117326034524088215157883275639196840358965993874436498593553723842091368513025043,
    57955817383732216854587833721824603297037740783035917523588543814899518894480478481680415418564588403827520623186867771178267780482356899479563,
    33534580587191557571536933906019648042909922029246023167003611310568870887405569655017531814845696258302267920018519905439623183895355011902573,
    806834594926557944844466926245445544687897031380181443815724837207849130892661624333725297228707121133091463714346914699618285329541947749743,
    454307276754064705443937650613614465490006644036773029166277487046986725611255678366571570919127587228017588419233783558200413221557702660980753,
    39682184627196682744853558047348076657383157847543496224666753556411412962931838177854906519886907718419728187010546988447985223545886081072141,
    801905232258920108203446574944032864441600677869797118818989859105713421089124448847631085380719056401148803169680380189671938433869753249431552,
    179866371582641106109316914179183996232864905198226482194685065429090156738674101784353665901341747751631018977243697457113470299626442020880384,
    131089227801371120462722765655340199907824193189184637918595000686127533120447201341892437416382337007314795256536475301090157516752819423560704,
    51936176731281071440437957961619935432604636977937096838797398466681098399777478309886460257062499439584108954975621325187154128716345331698688,
    38702708391292525976661595174056989473194346668259548919947456536794945160761829931715962152797761393990071467455009238637424718196271873293,
    728667837204136041385385502241755381258805485286329442610716861183990007633104342102767195444338631251720848532785568367267307067227791709932581,
    88441643649622527797310493378055845855919698837406372301278959656035585173453971941670622287033973971908289670130876983324389336066301541482507,
    33534463532119653256201883878544988362845538839164292048147973786011018412757663403306212693887714993650200071627566310210206264988573128207421,
    497922283960576816795131552336189081237179436922796974500440058602202636644678261273507738348956172540290482898737857478273316138495641892502575]⟩,
  ⟨197302, 1126, 241, [
    497922283960576816795131552336189081237179436922796974500440058602202636644678261273507738348956172540290482898737857478273316138495641892502575,
    161574983711702270420865668082444576409999045053690312460194028440784991294243359144699956620347844831835489850750276069588350723027926736961675,
    70117399079363142036838130007398532725828738875024152832433765776314599158004148126497197864048593167134275116247758773552334356960133924257792,
    1110470071633947069790256583746515052608804474509948281133254855797141019929500546375752576774011847905360200120824977488684898012137367011381,
    40165645796462566955511596360930196394244951782240387216147124475718113338811846711143075242252864863979153831630442696933016147572525694489613,
    588784302756785744589291304826837048634010597495724642379777674579646654146340543695050247425979578477008189725151762784872338127561647765585939,
    57923135761900023438387404745429081526313762350207697228922319146332947344375951145248562768850336261743510363587925678165422702502409422285824,
    311088108021024911792874703418340852444329338059926971802549077188825865911757521264851098344061861619672257707613493671751799034230079505,
    50695669492133364067647055192396700362382385440060194632036877740524723904591917122653912693967972059749819377216001669789858453201443935232,
    125024633809214956409517753067073288382414753923394419986870736508872200913552357168425849989873581769633434859137156119389332767931070506148875,
    33534446050961266348282250012038745430492687284842665318218271371000009956410002192530552490834069856207363416524975529575282808442048807447575,
    122094797628944965193360965107183739379639698356458351045671139553495995382600713833409990904764979505972803812252235575987473648992025330688,
    52008761790523648610339574100100193678174321838094870987018098106545021679830017009851419939180878083141126778485043093697005407714243096097792,
    893303948825805549822851929351333613357282937778309764854257123990238904285439420092850964311532852397798111120587812681468537215140753980784921,
    332295549409841102856497732339209227354632362360847130169384921159877700117814129427425683900119858604710675467914461858638533750286882516782111]⟩,
  ⟨200318, 1128, 246, [
    332295549409841102856497732339209227354632362360847130169384921159877700117814129427425683900119858604710675467914461858638533750286882516782111,
    31278522069631264447122017019235472045005015912408290381922689653751384944799060823140362517576727490660442098463246032262836872398131,
    1027428891138601175135534763249973899010131192650619354362690493160065953437972948917752506251954617806157318935324573534456229631976949240823881,
    39842949723158809010487018461307277849153630725801333938431193243508796305282798555002477450112001354429590536314742378032302820705483971624973,
    418153048093512124679619302530350489373223058715578996979490311454265040598517301391571757025861168210721546466384267910433812638993342544245760,
    582279270788858574815521932567996710054294688195583219626052689340283118845869870394568679506220464058608373648214062720556127450178105006620672,
    32749214988794029703066690359812966180940016741244448379773395408757637093582352352381732341143548976290064014200626153159271395849337307147,
    33534544983364969393289372648276123609695388434897645127957132418958506798564515162086008943162566981719231512827271252646518493369739199393025,
    692066977831247444401303047217468122250216417146416563897799322973726188671134645119980399604828154658006178027523645117298441175329656974367815,
    1039056946356488651628970920993996630860804811439132109755140308678279376537277294773694224339182064621519806685873287526236875549388311895040,
    52797554378528720482907321714044803454410430806735063342823013936970121796916896781406866063886164734367580817025352743776641131537,
    57973680076751943257522374187572240059493496408256155443624281818608355645946487032999590081139259288656175066127598662041761597960484599903232,
    94506184676234849699352990680449100801343157810737767910481650935974549913039199070053578320215322035154232486330323567404800211390703346909225,
    89281194231806049510457682529894573178823937762395124101791089590214156439034542756093081441326310683771211164748135418523188947311925177352192,
    271324322510327318895991676984062191505677482081573888246574573360185324966417591228912427918632006300203439168081594738770447924630346531881984]⟩,
  ⟨203398, 1129, 250, [
    271324322510327318895991676984062191505677482081573888246574573360185324966417591228912427918632006300203439168081594738770447924630346531881984,
    51918261971068485008897860341274868929818719388583736739421694509373243400750045033129885263207345255965913001422713644300908550220626980241408,
    40724480639293057881149697678523418437912900139893420740954628418086338746149395149625851766698066672772975785462136915329308356444825094065165,
    222579325675859169497921955740692780915680518198640647133853194077624175268782652840849415959741646793608362560213389012944619463729922131886091,
    33644562117739185782892564571310908469576032746552968990993767354044635364285865675143011685734010247424398442753262571291236034320086507465728,
    824698373884675646549180257628151485705571983139197664031572304508678709573406555054170068488945538597752189044182048794090822197397589871639,
    578697067586392016497000170527976113216223762259094887101176544532670425281232273115303435788877841128811567907472951011653824954434060325,
    38703767418027484600867126025445106854825919301002423856363427341164180971345604767402368830892559661625514951448347908181544282055473365441,
    820137223014131544644539108110664849168312453431008787867957171114234064294523512958082742724485198227618719532457715658591344665137473524858909,
    131089105724897913967518478088981371755838106306884890438032302980502160001567371473441188994353486536703164550412988979097602603190467077079040,
    295852541946521774039617066790727152861474745621234537056125619458829644403729409561131912851576988710843871551002103784327129799718178002056192,
    112797555316148797792372355260978971808314899821959597716009385826111773043516201433920193405441193500572796403458629832958074464230598197570560,
    324714294369933166114751125802682107006890430949996245161557976700735696154687237285363783298341862534973726132284365425539933149930982473919,
    186710796727784144733893546529784459045393142713073938250265316574129274390220620435142497674776490522622597346271166356276267823540309448496145,
    32839087542963462213973239945913200743309302401687332649330474902505116886176180676518974189871265351286322579205960596426332169902482291723,
    33734698889888711959213083903545637514888414560693852741789033125717799991594187268848785947071546553188816607842568487172602200575385112947725]⟩,
  ⟨206545, 1130, 257, [
    33734698889888711959213083903545637514888414560693852741789033125717799991594187268848785947071546553188816607842568487172602200575385112947725,
    58956165810522818450463079380113025237742930643811468586160412244247690385105442782312934607685493976818880749852493041572246866306360130343995,
    86336927581529283871773368626899599774146059337974749959465525162724662659108218697178600460945125100843143628598391349485571092776690402335,
    53019733515134532373111750121054406260728829690276750303485448797981677250015708648192852310501977606268551073346421119361966019888586171613184,
    172025122966862136587253622476488472795740508028225944062523231829150764162773755422074703038939019798672745725566271066242376364413973547,
    70156151244019002771101013228622088439549764038286821438797406376008231100489144387783557960693763731932926713867267124538753646434827013170176,
    157825760640956970310565355024103812679893087995759331716015713477058051288472693938628367725015640836837462928904063085627654491135089355913,
    125917773267731014730288027323800308412637219239977880965822740837663354407809897441060166079179081579737995843335307565212769132186499518909440,
    607242517564874741803098738586446973506957714162268882785199802714083069933311879560456601350439076344251263895439387849239481860648267094701153,
    179988501197583982091032197551702134439388216504352877252664315733053844385008026534400125380748491971387529567826122365953377482296889112022016,
    33234658943049277850863444213931532924626744627933293626420700624353954697245602014994491700395952350536639663734262316399236122087716290571,
    33591185989198450531339600938496065580294426023699261777861353054788071156486819780942459347257634187248004359176603734001274962074688146123859,
    336447830766720587702125875628457169946233394996794489963712343723201989491836782710505626198340823695868623389407145053878279453432387753091,
    39631628632529130369873707724773946545131679818744395639023273821211868622743735524724277809905154933705355361033142183547449335600058807091213,
    94506498639296270648153152720466482413724278844269435272581985949300745739100367752315264794773315972942937482830315367330778359555117921090560,
    378095690686640651482825567380164961350894948384957212779500324602654596085131422204740038479484583741640293650078068195263213658544817630225]⟩,
  ⟨209739, 1132, 267, [
    378095690686640651482825567380164961350894948384957212779500324602654596085131422204740038479484583741640293650078068195263213658544817630225,
    399416081980975272627668135647941040292478423060869729700232237839366754552219439992624640760285787450558997020863575791805598335213974412328960,
    240930886795806469896334502635420043889710429338481142444683354293493453711391143726671768837559379483256467293810770186253588147035690576917565,
    38702773723754508925982542517181247316081991898480636153006839161932390447599331156819082829340043455214371069104013002328617130555114312704,
    37795666344140726815370544158267885808415077447980156204720840192642346346112615701610810309502773426661534128183483837859095048505803795,
    51826185680780428751755900937398588642502877335296188886484047449157354779593965203725376548679979589117433158951305872604236173895030463791104,
    387204040105781860233527036108489495890608737421219732803799843640609323307511287992761093660697474168701599613169799938528452352948113037603851,
    33534457847930511691342803703735187613525694847681302155667545644561780331328159413737472987475910538543591319330399433015322470066221072002077,
    32171178378211843868787343910029197990634738328975194714407976816731422923614462685625030316421750389640083577938029697337113835186683904,
    316901683828084512505648383355613900508595071592333007088053593095680170497720306256827844293201667377702312130213329076532566875573507113,
    136733695894827461976155221362687194675413052462093188582429888336285671411950229283122970116853637617396241115456265789989336298506181783,
    39741852271288522845309558795176306643905793385949950906961248730089928178570477057373801430174979051662427346557706008133210182339334811884557,
    592449182874043560671175854204964888331621443623799794360931481952200453526050236990411179272054261627162775123048162470232079495438845083871,
    70117399079443514209797130403978094827677455441398081794064464399218813651189523027799821509419211450842201508734704515944532074245029793647653,
    31493137361659122347391170741067341031057238763240427969815735879496087224005327782523394751202494948491811139220218927846943358976,
    56655877571419333606142779677707449309615692602954414675008572183388087131913955796547541223288958918734206697640854180070374981913866697728]⟩,
  ⟨212993, 1133, 262, [
    56655877571419333606142779677707449309615692602954414675008572183388087131913955796547541223288958918734206697640854180070374981913866697728,
    1137160000821704393957764653681535393693234894298481657349776813429882947545288165628277171431946289635158856588245533228040281722144720384164033,
    32786241175526502858521031594095323550347040718981077651373529738072433278077887808162769585523788187976832490751993101137620374266370326539,
    33585019489397754281742733790086150467946811144005437284738564991583228053946006458405595700080874209753824608805430781688574006639770391817247,
    1057858183345660070359142503987509887392546946307230517270474914053724038294537429981523485044602964719438503221725297873424272144167865949369344,
    128016650868827387091460874913248035510247715009612537070471073791508137887039288350820691182571455409113281083435072070063363558892437017600,
    694912544719413326716846694653843744357809118703660041454102237639849476308639481503511634250046966554655816306635820284204635364098327575,
    52275450684169350431644095782824607222641583277606395214803484405521066505342422068798914302966986410205152176245234190047689607981610947313664,
    306644567000612971557221167312639072060306207241752885312133973643631617519068486553451483310349788251858333769159155782805141362176406061075,
    39700096840255187789553368495740357247697407941821264204456921752404472253895497733079414266841412585751854719095571632548653198506765788980237,
    30499401010297367489710946408474042997676278191606300953312011241939035471680557681167571630564995943320085560870184450465841807360,
    390263035215484039761813851665740727858173519086684466207359789200110732580015385341121676313793660347417247427452317800490947154594682430464,
    88548819667981745856923579448664699326838466167313555459652272083904072176880959981772250796737889463142184648602446488282283265293108154252401,
    679866661374925029128157690150132193053872832228669346634074147922561968604034681369538703236289173578282092054284826557024972049799256613307403,
    33573928036478029075730738930777718570678806995581052430065951167922541352258823961039747955554175259533899355160948867118052325725953099574733,
    94717467940468544132642649771472976425711383688164762074106383337235305340517942812726032189150672364211567819233091327883780562721123933066439,
    380863491712389604900954714557886723620363469000192372089669478990568331614388005682702257881762088717326841726703710947810592179069449289]⟩,
  ⟨216299, 1135, 264, [
    380863491712389604900954714557886723620363469000192372089669478990568331614388005682702257881762088717326841726703710947810592179069449289,
    555342574078117574737330287957628393584234736091800596406929098256289214954934575855789279316073880887628073638578903236676163814823048235,
    125084176389279096114259869669273665528199561345428491807234376869031129141079550061042316180911109819692495960151975527932633565713050136239104,
    954263610194215010840970040302834801474900075692726826357203425707778895553766221746662882064113563164357487640770439872357974666038143748189201,
    50611234152775706728952182807246265723914115627033014810031477972951620832289155051626326557666403845894610772269019423262626948131350118471,
    70117454367403286789063403969237724098985025551094192839223933692216634128263631816957689008850986227892178311438204757374165259556059567272989,
    39631658469724062709781789954509912336862815084696698980635077288555275686819948471850369772943173020733282598072892450208979971274396261154829,
    479571213939520408520307840342894784931101143414434283696138159172313897742819197874717386987451909398087575333497637168984014287952121095537813,
    51858652433748358497892497551151074025228502503055591801065581912556800972253355341042846020997893613044254297094528123525256177394449965383691,
    33835165451488446565573287868475124634030258473630027560768291149677711979889084438919426118473248914430871633392448913124249551951171031149568,
    32069199907355369412119030086487151121875036588583484443208231394353059887641995946298287961704910426750040991833176053459038801381818727,
    38702708438691064856052461024881536554965627074707404229753606949270424484761320199944274781871123335831422089124718652444722737733977505811,
    57923106601356008865485576488666963326780653783701669881577170975563948831004561477895083686577503713256812824494536776095415391290549555167232,
    186121728776258628924775488523690931440950101953510060926947829682943140330224206201144352233825700966713579768363751697372692875805367076913175,
    856738541610353552723130077199952490683897885664868782399787991790632523474951263125812918782733512982310484535797248112331174543592680524362811,
    222546618529472982770971326753390133049595901806409815704173605278253371034655502125064363025324622844519735250546974841967266008327387716025344,
    68907218448720266824567099553113025032508147643942443597839212925925548729107426577468952208055510937297548950949401312007057796019516372131]⟩,
  ⟨219680, 1136, 275, [
    68907218448720266824567099553113025032508147643942443597839212925925548729107426577468952208055510937297548950949401312007057796019516372131,
    110325396668818757225628848562014105082076744418306353509993744540452407625009839582629557198861963877194596766773731704111104169899242595645,
    161574876204703942237481674750905863346499137481287207608407695576993036556236999745110135905077935997748324023270095818588618874170880543424543,
    39664842337109152880681763001687056023842692268043363136038750483160078113151628362248449779626067617550004317120686659527817883598289053828107,
    33534408255544462165239719537482692294365735375011350492874330712739851594162521535829805437471734792003638451831639890476256922666049165339665,
    50643451193913134621290435629001793915469629654158913157703673459534779564758326578420575924956239401906046910020411815435707471873670381568,
    179923143518867303460595146424514079110497631689325229136830925308241714543505585894393777511295428504359588539162533558787610932105833986753536,
    108171291299508718597421337454891211035635936016421183005584450930353012724099721366056804420859839666910777048800236289912140691032506368,
    112836313292644853603747623990030965768521671469158487275744408597784688494934377812006895685440937027683758695282294032342628435777406955963392,
    51825941494200709292057657378148746985165468751435851407778976822495434852582151294698066599833673489820163493660984433970986178252732562955264,
    216449499245403950336484169848498504152738359830194406560761258218142245174465040624858923948000567785123180633671170642741480768916592639644672,
    49461973531311632044666889383103971442008760897275888637508477676576878593726831803122440238238948149905067784622248437512683336214000640,
    70117399133345266323975679408212250548345516069732564061670945970620822105166336377917166733166406064787930038842654019201264220053640243637375,
    826794170039785659994254251307790516956208413129178192367742412394267309714022375895087147574514236589663509204815821449135568422263275794726912,
    94538808074321375011427330528708774533226995385138494637971431177802539481475606095791209261371175339593206316537653044048864564767791535620107,
    33534408701766832148170834403520606199643187343118218692263272027113570066482908599257960108194538846037792293196226001639779516980392324246528,
    39759622333894401866120096052058433700019577756469166621486270529824401480658287246922011318010611278236849898556174867783842057868201398742029]⟩,
  ⟨223112, 1138, 287, [
    39759622333894401866120096052058433700019577756469166621486270529824401480658287246922011318010611278236849898556174867783842057868201398742029,
    308000174250662714703149982409825659450628758975403823732762012682494035119695606089921045635030160507815055338384506413890835145999607149887488,
    131089577158171242047174855015675756862712581333660984177102292904078419056037459213420771258859589812846995103878201997433919807682099706723357,
    948344456656110395378478733274996674571886674232444680018843582394305001484831725883452970944963536084703444339284781597115919079887052496437248,
    241342239578845383067718883108245018064291762495946669362301758328808339561691230550150059976651506496275993755054677031354475794149670935,
    38702708391292504794465803362514313569684199962755878457557716812184080083624192373022481748282474554433655416387704617817708166753421361169,
    1210337928907283004644311212573304356795045209502285887932747450751369483963092560129271038764098982908830706391895688517013532062101182064099501,
    643319396059864104855838326028455104083180780168245673321481859130944733830531032126506618832144377065659636778527100234487208944324384237047035,
    36990232470250864717554593191832046254027357290518318403028085564383844017810045917513668968129740813625287566166425508159513877820805,
    314036753083699824087204275983339000867659833917847238905135663465926635564021352622217748735807423585668344730051057561718272744581764870063115,
    34049451990093263990129772765164197901387210570626655375609411954786586910635527963946428834585663460529637238297626213344615991389996290419923,
    125078254107317041277301140761562178603405453278643890903815361563723108828136369903026481630758413975149391030645636339921556040583690281073731,
    49615424161988053994973092883545967335983500186402356976623280619047267227871711728114841834107781948744386044288026396765434017449331755,
    39753636073173153249022182308244866235684628952209022102472916598669958214399062172106412731337624625423669264656071434937856332233322866439181,
    295712599288794045545112670735072667439614661686844523348776683307508771373891402495267961326229870003819023467892443165955103449160003281255424,
    31977668011876937717993168485945984681322961542074855901720305204129745246869289242817661744656611821665202506001228025631515531709621,
    82337199265855741564983294918324326119608840966693426592286917433365004077592198671932850683270804525117092611618538111941188487502931]⟩,
  ⟨226607, 1139, 281, [
    82337199265855741564983294918324326119608840966693426592286917433365004077592198671932850683270804525117092611618538111941188487502931,
    1084443407232765607742337590576391889320672459591376813170880948079682887074103334037057344676612393015812982049482222425386350093772259347,
    57961771513501533673694924213712318912336385048710406603382689516701161989537008463939587020911945837575472426385938077569076995620217248209920,
    70117436874976770131105902694389605556382863618666560248676358129179021124376448016492790322682036986141528141467508454771233948854287613492363,
    32748619998831330688828857018886936812962363791467082214815037464498782577576931655994995034129920259224523142651111334518688626947034139659,
    33942275296073309948737197262979577089497062304158542980615957607398626226729697534767291793678832221584700864297129996159614294331628293467136,
    88519080334655235269001781360894621738598399584039400041217839088080321330233396100096386864620824820837911825878540991285618991963616215826449,
    50678103442919005649313641133635435813347589329473395996894354734753266127375648766345686807616098382332891245475066895342994672820782366720,
    711534456383507827162175447300649328774547579001495659533332746699723261553008536359048327580596604918272767614017906837498086608259490250789,
    666247127116276590249218146910784343823323563336752117573836377759590554728453895488790475307214537753079267763743155844017013559909154816,
    40046246546191111103989229225200239729050197647517618716846743714360232022994433938600446395829985507130473111769141791778849075884468083901453,
    51825903667657725973341817263232596999690933187306809689092318525339876211444893664522764287329100672385567202097043571488347056887032549736471,
    56673069041419934457293198885742817973615638534205613685586748017737870610134566307611890892908815664631507811026285147739462934807352470569,
    94506109053740321644723745051669634496797008440003720655150798998814217171284917780513727118389483988954108154173531536703165776075882719409152,
    68529656979495720939359115819555881082986629258022223316467649532430274398301034872722352780096722009325427762738814220294922836289212474368,
    32748596153873180221567043326536848112960646003682240237434701105376854836926924401395951037454004733180415844593499515267283326612606587915,
    33626737190119341758392155767177178152203886788056206467350940977135586353410737282195041411510406236102131364401154148384091787017206161746944,
    31981572082511399522334458900157184813319506688565681873199709987827452144422145755812422852006460092365407085894418256208811338452959579]⟩,
  ⟨230178, 1140, 305, [
    31981572082511399522334458900157184813319506688565681873199709987827452144422145755812422852006460092365407085894418256208811338452959579,
    417813724925660984353974054441036897614706084590753604355153159617738016412373522540026307050342315638461194096401350918544553604797089200485713,
    175651114084548045556668411486491482632169891775604865227084040260627476010544637380446024595089789959103832835614032010641586691879338372096,
    1423688865106881241093961914768207341691763290231861536843499525907778062736136573545185203017720771340090120331772472230152777751531397952045075,
    57923068836003056161327818307947210549478494416622354584669133042181226142478870196286976130981343000477663687955935285744693560307815325711360,
    211495739637996445193290111987901854957614479847558747707820185298612196625324808608004966138464051650032775329038950319189244361904926753001,
    39631856703660154056042804914600035809032674764767326067476605476850671386305040609563270049211528119945326816285786296535793151803743498427405,
    204305643422819227901322507729359413052969983206349803519248315094541478702933864006824711969378416205077374900068256787335620348155174392564736,
    136693946801609384137673199955970982354964794387606076642784086279589257676157901839541778732918374846007663147699070049696991326906613813,
    70150148510317962260301239982221145469687868218216271842090921966478424148545165331816009400063596290486968030424145294100513551741164914242571,
    33662424906180339277952907703590628110597305752098486275871555669835147261602646287888118809732897151093704828174672731624377119771608149404743,
    51864638357185916235209390208791532009934768140144565214482026279523130288491607964330613697457842945396401886393164237570064410237945010716672,
    131089088330971133224852192176128435920664386549033925347749440531063425556647316557495749928230693449883534379123954738641657136571711657888965,
    50228633336928850488689856566768703590184612480817760534131670829334789030931039254157311910138021796561816411335065217345034416108393472,
    56565533836495663661337085841542912276152183675988731721249223069270405591024498626936053566581120571144419900624166461096984110582903878745,
    31267480192594374157689202354821272942891378248766696579541713641334900260092338120624605830031708798888672701051312768471313399414815,
    143283435968171426973714886551847889953101269728734833137128017922303252244886838138722256741997725893699611504887245463855464658209988822434019,
    663900305511936265226474763800073627951729021522296075579197639119930872055536178249145363373732053574883347383455210143263441841559830873111]⟩,
  ⟨233786, 1142, 281, [
    663900305511936265226474763800073627951729021522296075579197639119930872055536178249145363373732053574883347383455210143263441841559830873111,
    88697676238599041164596767988687330809799114481684340170072696428445105513807191413411752456059984606550808397915394673886113430007094358152299,
    39631832147269344361074184163275016014352136855100384889740862554965810508664441245897946494100259057599813136530317022172048180938860806837261,
    33042142437492652951780848953602142528061023248440190396099385908377428639500294056669621083906141405110593269253465418580204217110944175115,
    33656470776996361946982341905540282376002078012659233667114980301197048507170620571054550159926411729852814574738159576942495191903740003101696,
    32046258869888792828345549854232886417768304712465076384884820894670595093437779025610590389295448364632116926092475996827367885739453459,
    58122713958125882305952950740547555286715859597360384344514783111453569961684292620258863514569784175715405307964984457607391512301410115911697,
    38702708391354908477914559443657802227601463537240689179758305953559798517690153627106512071145192303949896655771561072711042341163927383040,
    139963021289747310903928811137373639798770719981559170974624379811934246256175100158495628985449777642448407380380930674140010959420141911040,
    110941786949841328351279136146369031815513460129161736561527851209477244322640407084098596670018432447391080367414028390818544685030267008000,
    94506059665617092232321472012722317732473290212665862770860984493513065207606901467918622204738239025920494384881407683274144655634762545771549,
    51825987980678391043067238576197241475423928587846023553225382075845442520035730345641516684971388360567385973202147613963349424115015872805925,
    1412026635984014493653728356036118301996568377228098988192043685914132254041333097532352111286895937970394771210678106463256533295439160376581120,
    783578060646724598141910535997070020743661477706331562942566776094542000216900675326011369815192722177902392931480752081122760150293530853507072,
    551826193374510183437432315598620768778134252399413852684673337369846940851330361053349344920795408057461765116995946680179743094754429427010571,
    33534516506336473621488851446608743524007073204068761486656872459708254213833139403862090584354398264878574483158155844922328140736994293591053,
    112854152518578699712450036637257608394483010018865448538427297744945022356481397555967811951313851563961904684992091976829068928474350288727333,
    1337380345349019496216806099034156454762196572738669622846753243573814388026884216825691151936351640260007537879100478558642357742540515484719]⟩,
  ⟨237482, 1143, 286, [
    1337380345349019496216806099034156454762196572738669622846753243573814388026884216825691151936351640260007537879100478558642357742540515484719,
    55628716028390319335089502021784210888330872184563335675270014894696592141517997693961366102555321375734849882616533444633566482829186048,
    399450720175692517961863504693898024621695692481507888712727520155327617744457536429414364808643071998102155986604045035143909416223951312388137,
    387209162859520993311054106967338238334771915320274889073275893985109882575481590837566809294130730460317894885481433311876772841708453408873472,
    1167607161683522677269450985273364064174687326383886925220242422941269186896942388074182375336952982599378418532687849023098031756131530311758848,
    53975560935450021419736749385360343833803811953732118511639146438042292718980309894078077115009610541474664848130999175876681353134080,
    1426775730637363747030376115236327883875126437326303952895191430110405371273277418346566584998058778819435369645462640976769692735940801344529,
    460386579185286617214374887808928922336474741121443695236148690012301121428816961566932007828728334554732636255829790388922331993865851115667475,
    57955817298519875435554252619752826178970346163674786654001021206860945690815695993070536158992935718678818614464658666416410236883839170786315,
    33602972405887855869692698746226657604499982393470618897249198286361037298327727547378519863551475208525845458077768051852115831569503881276416,
    589070139458499832727069189432599009088181075071006939873863363825658180327954456587795015615615832276645600963274441772965095674582947278636145,
    39933243509472009213340351044461047390939515754717519148814840415763962422015294161928338583537047998840222828377674859700331826911770566599693,
    545696399183623273309212050219643210226661437684938080709108313637037878821268502129892037031768350215800588001716615277242370614244463615148063,
    88408943916650955721138936622903182435561672187738311355000762482169018942135405810269995166820448041265647168688824257963215580732512208420864,
    31278598980038256387286679173630692786565249945090928027679669801271174420857600970637810635699669264577064594482697991408877300613431,
    236306898688090559009840380793828156254515455545580610257895824477777656734464445743855645236768688425961887943586279403485105327343302344704,
    1094479844860219849524021415469503480298273831056708330302113704444756120519518288205559978771643951425978291352891381206084248121691689809103872,
    1306998637237745578269542619608043060743299699577162674811989865259295746428539916327980221722116225895588414053964411137484399004762966903808]⟩,
  ⟨241248, 1145, 302, [
    1306998637237745578269542619608043060743299699577162674811989865259295746428539916327980221722116225895588414053964411137484399004762966903808,
    271380415434241633573588635336833657314482968066281182526157594764096827456254378908478229661315988065171862333311382833393017730255497678838893,
    32902572281390161930440602568098827007320706238773456089503174331501271914649472001412537296864426274841906358534549240702469725294098920459,
    33692252104608103604351167864323452468760089455349885598423261565646672364856946520077903646777393188571561280757850526968778070432732486315237,
    70117431176674905373192218472789367382065489408363916474821966069695448246348535807036018060807653422988460346037577908821633334393332915240960,
    582722863517933491263890678149496021510820105179235801766795388495201876501098073187475117160838759512809993499737260875811802068493163783258141,
    344489915303200961821516060440405034086801159975539012404843851890855903450728964683230511322141982174718091789883000652626284181391234434135057,
    39682184681225149174098012847349926465678272781620958824535413074536775751435989231049713400691387274730780933431778344177024198460141539950605,
    161574943039795928328894153421588419830863410680618371672359442479559930449989530116205096016581367807996492257380566958357184060186753498087777,
    124991885315439134485759928039100348963753947812147871691499658528001264444232392245412346702454623829930527970378963735184456791910836033552403,
    58015360625291141160899916945509834206837534659157860530395096328554435389929461447009718513138359102554091722239145597885738658167450864993333,
    51947966055439154584377085868237534714587058257867541830014852145199713749838406459007614504860396131684163025763714252349913041549919365712896,
    143322084540239622718502644867571136838121715146031578259960131168150454416325512516129027173118419225917798824464000371655210811996874818453527,
    240870809828116258849830358019722181345177769507954800871225997042468849535627695865443186706400461334198074028566062831667744174666867435110411,
    33620745066421467336328796250746259915174556207865276098287764698307372137675669609441412541086198713426695100145503854403583199542630763473957,
    68506040352984752707357266212700109924548764504696718248537167235664733731948606757320340001377628262929093808646066454912001571312381211731,
    311087010657870368015374445795421859794505225508689834551152786455080421034298718178515837055942311771122579596501608825495348670865896507,
    65302439219186355230415276795695031021971235344430567532637809192297122160507171913190894392947542614243506136062077858177443937910863,
    308171911791520552947525282560510583797848805945397473431834975123602771129125501721231561844400200178303059111657330039356156720641906002906603]⟩,
  ⟨245095, 1146, 321, [
    308171911791520552947525282560510583797848805945397473431834975123602771129125501721231561844400200178303059111657330039356156720641906002906603,
    112797726606198222248207510448832499204079030908269335267437493912767014616076084359548154038555881005245109021808081150071274579203875347336192,
    39688903810661625887899236696810164794991420535660364285975563939389247487068694554033216041835064293760679605466521611886736862839655425376269,
    139925176522287520425353245161508553869583892444984010471642369733574064819878898508004647903846589483131865073244968393296848401483749692416,
    55799298937243142165793758663492935109855947108625970284103495983522132091465286077459338908363880602327116811256489671626204912402038784,
    204255122431568133681030161670689445345752078532406312071309835127076774397773639020764318513422537566589931660730832280270022270659708855548945,
    179900309105909263167298866225916345511964607899459464702498966262891197759529438017943210170217436206958376065015142624447000006371375282412555,
    33573111012191297963051474210328032876099463275467182908693032321976997179148230355181681947862005709286766869833273248357334314996319361444864,
    698574987103786147989164192341128354703625973448174890989867579387585441010603893253707768262063411610451691613552185489493359754672202227751967,
    70834887957571979982927897540776992155427999481601936937782115052588360465643672039672643910023049915059557676949091321839033121446378429498368,
    52591605041524044921071658705729819071525491147457469073146414447850727459066228381664899746559807720001646078839120810660764308905208885294099,
    57923068804727306889382852850090165499430466573000635095160827749357325115177743507976791512704619726219375572139903403751083511737215835176960,
    49456627823266894156264131751838010159979697964958342353908321623594621453403133404355008539703454941928205455799660797518692418127457327,
    728611300780852523876232611240183259867539983891250728449118917731579189391466026903790184822744320109255555307492521228608982780377241255835103,
    862748867225502578205756388237916463193757100807420075932134095749994475892198417703929993837970438241589743128215869679591490869805956022221824,
    39631750741396625546698983518817518621004517343724106677249235721503729783952783589592173290003251784098594842695376246856864327504130241678349,
    1063955316465736867853677841471463599250587587714179370749046074066426165870108193670279587034034361339722735720544827017259477302650126319222813,
    32832758853881426848641303702669832794035049380962418968515047547644329388005033857575503694132350265732436100637265095675452046124319335435,
    34335376349849088900511791621532613733448407483830402358820461868547789288220191549806651838745871914047748019900036252749292597142731844758528,
    32148417481246765987273454874330607049410378502684447751611172137806866930807747959908643773642322840707543971692294765626696958386129920]⟩,
  ⟨248989, 1148, 324, [
    32148417481246765987273454874330607049410378502684447751611172137806866930807747959908643773642322840707543971692294765626696958386129920,
    94544762337098199609264249406552737663790724905415581444886513057784244195642579766778789049090034733402125897756405139188090459886726188892221,
    844513974813518895820832004976969991328002367419515355888643496635223308682577740714396030641721419133288584831548324676947370892390575599779967,
    65382678763879686622692214024320633679359272292655570588871310544654873668502736567419811595005606476110133313352717219734080692682769,
    50666506219570415143562644037531608298232457507722699032789691919515700582196837482832828846220045993395946948900772863775205650212647351296,
    48302741047309636870398142235377530241681149492011131483912647219774961802343828011836935009996346745248463744858671895107596625903616,
    86336811057274766171692323935901511195365440460101013845289852628340959699528497465471325987979558243275518266833331899025932931061495551289,
    692028642107890788804272943418697172033417933843721733171992745288080419134691745120750463206019267905041962122359175233832452227513055414600805,
    51953920372133137998029292971857891310829171363672972423720229181131908913001003028578597126035820631028625090180594771746954437821845178709435,
    39665598419899107306416761496646609000934436119980349472714109422424156117651345321829524511428226505646468107210827686036744444133396974665739,
    33534457680433535442494044265024240926598230517872025657147919785936380089501115629516399257687563085672366398966225304844649795073659218439187,
    57923100867979566661242846267629636948539829001821406834985019643651259545674655751156831522516826929331674654569398928342330653171722204741632,
    110587146240098643381065749305330138600127387284181087046443787474819023257580114930739540078505737737291036715891530884858188832672533446656,
    70117399079363250380611299431858959505623953504486491776357074242874322986021795756128899541192616878584615854589231765385280269446461891019135,
    1222520449389923938791033507185011411101679187030474618645447454844121110262239142133312748845768075630938548831343726385368552763942360553881637,
    216571462590392789247543788359642827592956240786208828714837377675357077707211283163779921383900577379430804569450010570197838512968287103483993,
    324507474682322026065830107229924013869970381649720790226901129631251725866272312240905172724658829673710878847167357428432537738919380254720,
    88408961397473787271062204478513901061942309134175016960872000614581983434788032377316751812625519808472938191887972470345022549292534606083072,
    806911142369992585248934455119278306305647329266529188306687165670935263315535888910136824821321685880874367926241692223452282933446322421760]⟩,
  ⟨252953, 1149, 316, [
    806911142369992585248934455119278306305647329266529188306687165670935263315535888910136824821321685880874367926241692223452282933446322421760,
    112955343005758980143527347705979198211036380328938180438126766391415018104050828145677909081816316793227010528642607201669173740098359233891591,
    966433681468759281780895390325554000326153603995270976605566220225776745091369871835946322688611296690664454649181114239634969500186119762942987,
    33585019662589794131831095337748081435228588803278204227665095897419599576835126129755492257935410467220455382145872295487478702985738602949655,
    40474133612218502122207959178375354796341243578644722451204279015661444652644606453669686914688843967544486178667467084598608337537362475133965,
    1140297846385844445772257442813013693634839755179511181196093509840587015412325112381086107685674686303241020492484228801493392571385320046861,
    161643350284027194273685148582959781715613104468453528353711550472557614018141643567534637392468856042372427625629800422594055569364453058167875,
    52955629286842351654579052350182481653032092507106542252229726633650023281308865709921911528181316977399569798439285256140883715471799718425793,
    467409663342684024132198970523131120997921169786660215223472701408242966440851754623066691274164665825116978309428069329102944835147021884445,
    38752188337427651555403382422620665447893619537130024363726742231313163487034048844665011729706262963800252715666142637037127190222993358848,
    37795644225097201634126908277028713028541493514014761797691370366648197301977447197652449173671086114632156179229950581981264953489794048,
    527405240834328819741516819615593654456709407362434038858330467820562720614008209222259100449176766886925436364402127696336025593341189890768915,
    58509563730300147604299054249347027960127648619388174438808326476528311085602101782739809704510485911268212824503144581253054656769395270890537,
    32960906803893277403813630969952544568972522119720585166372647548693168376998569005419415299706002178782470685408704967929621232941525941259,
    33710253801674294769956610771102308237022137875540602131236923054882799426146560055721531655597221930800221355528055832916336388118831657135104,
    318585042392067888292324166361601490655669565551885168772681634372393849790297154168599258471316536921653941363615673784429274052956912638976,
    503208052992246307614616595643396167506187708740631739500154029452556366331375262973859600661630581939533970451720580269960424231251795123,
    39717910649466785986772607671910288881847977827723325609225248935402592286608328138553408522705843424083677501353314987772378757570989913014285,
    70117399079465695573227551650516892599426630802533892789228192383036794912147986915913625166178877834814076246437957897766898861925477825642753,
    408096717196239888781161679300815708685224547971050416921564743170555521448934911232714168525037189952041110670926727639232698510088453780497]⟩,
  ⟨256980, 1151, 319, [
    408096717196239888781161679300815708685224547971050416921564743170555521448934911232714168525037189952041110670926727639232698510088453780497,
    765244835970143910559195960127368740335089723308321037069998447212426879538587789368740266816395604389524800314063261059764348516467628715297851,
    336971202945268353872080803366743012608517893135375924286398670973582477320563186364696379376570173411586759800923242258805173564204103476687,
    38769659891172938831275335671887413915362238196862285064090957987227115425051056713322241665649215711623868338418994918898226238292732411951,
    935914886737257888979370359016619939627822845330744700099243626091965599334600060301127379234687369723124859490085285823121338558975250663490560,
    51858707352724131527115367925805069582190219130308322632254135248585217463119446903825153925638576208144828402216053852287629516965281663025163,
    33534725193941174435323022696971521371651506987729017581324314396520751870253099638149849314607355299557896564887976472679693284787264341159015,
    413854119224323230176392972502971730052892634075683781785579165647341709154651306534627809834919770921349121823980536887102991647575303789591,
    307164952289435849783102903161001506873712819209465927873425333380820738359685566997018265198920127024914170721092574396620058769573467757767,
    88408894545945366529646784807423152788516312524557257510667248919559985424615828380761716937916861696328070439249228038336976632737583885975552,
    68474022824025512483261618502024312109149333728264323721748150642409829019895527750185165848280998003642469917136837784950305940370732725248,
    39631663551969440945689116225424151478503794125736995336504748875487520495376381619996830516247578762513825117969793464777602103496263779515405,
    58033464042795232663308239014991071233047043375540463833684101340007225009050686688664749532091187026151733010255838838242168590329795708977152,
    418403071892634595098924561354902736951325175751552587958505370124679042562281539461984302909939187179899993302184348954603650635666938121030656,
    128016650832798927208568148356375480825525338983802389796974638868062505067477879720597805719539880115983007512491033045532628785119492230175,
    684250569538728187644478648552193120767802911875718912962432694874709267447599727115866848378965648940351433260435047196571350498077977,
    131122127429387799306946743340519023847621524670186559951965706033532287998430381491292192382300967826013793774711376306862103886898052325179403,
    33534446051341121858245255875520985450634831216390987338363816628501504582453401091996092848188448920111282512919555656811717620080570622028817,
    240888666139908913734094559720202318207466475629127667159671573277472083259747786460382692392929155604924373358196920737181619889826326551823389,
    112919701779005620219899536727159276021276886058816796779387375705905842266452618409316503303895465357196744504398351842552333063626104517964800]⟩,
  ⟨261097, 1152, 330, [
    112919701779005620219899536727159276021276886058816796779387375705905842266452618409316503303895465357196744504398351842552333063626104517964800,
    177550268996306113834777290454761595510323056007589683629808503294216041441888714332006389548171939947626271948698769609551642229869661585,
    300690273005420230319985305919493121815615254099617856758924524374881905307586760223143674433736682501498869666236630429133983293811913147565,
    51882469195746347445008519733617879714241123851584821014845341144047292385129280993656783026167686977166190941813197158540658326289720990049359,
    29136536629406454560837570342101401744398871073803373418630823216674559425680803180532017990323238883088933875551750759554048,
    40849270761674597989405013365794539879683675541314637101410342616780166625891236700129996750916128980701789260713886507367760381369143335009293,
    515569966029186846091185423267537050896591755495610016632692703173725237682715441129269488774242267507476744455798666323483183693945432440893,
    94506126705132036378146948373608147827090651757259218315741012164234227450057823999769279541947900838615633703270925106343279208280534228763691,
    893267441065443616608813455861724586967897445510353621625520232007931502816951187175758616060844010374727883484195316265242753397429831619051531,
    33534408309356435790211419530655328286127323033446254028684625681035083955778449649337183332194551268902999807003145416935922458912983149980672,
    1460309785081248702384522528122375542019986153243469433423008026887950041650261199749077266501595500177756127427235452231708807474958057495098441,
    679833950713673061347955275749204998239503868387092956331652627902722860298178029048366914765735340570991050557460858055809094757810076747038739,
    58747735515591761298393610314837618434416325351239626749759205455936982597088589816175049481174332688589108929437474574126247206162503424183463,
    143484072565501855138563663421638942492790648393241595484734924136133732469996668869358703967264295980776973505251891122161723899323254941168753,
    1521311175819118585006635655134861979599353642038913158796516872198806107385912744298862345390624564492820843935821278869174907944887061321875456,
    154518530880927578794696116729610098810955439799651053803236359739460415937437504129024040587307842033911443297503336911798966101343207441,
    50611299382603121030348606512621993096029420681422989216212370845746492359849844752835550367242325073498319916756515539192218315162502823936,
    1254381226113478368103605199008211466758981935080690152083276750317452654149830565159764160271133481918213018204726722328370091372963147284589,
    39631573480812847383889326652338723759386642230126285468694806013094222127749096341982138305340940641941157797447759358584628248220861782375437,
    88441642936933307960322909169386801517176185812361414357858311619709057502276715683647969186065617484566924539686543624508691932094054465029131,
    33535103113436978203950107670345206862138096405945838506481134052136305357621238505433211212879491856575740339567058399999170081731754841877504]⟩,
  ⟨265277, 1154, 332, [
    33535103113436978203950107670345206862138096405945838506481134052136305357621238505433211212879491856575740339567058399999170081731754841877504,
    161574908120305810720757650522481664554153296867172341842300088876635842728783088238188359383145409141843408745456930490674111077524052676444160,
    710376353421547784497928899719551423292779584853491353130263017070823103165512437966526904812590642712007787940436788812580394318686445346274304,
    399403110470467873484234943250688811206401116539028352205298360540420012334150945275447299841544730037091312632277523100711874287282272224697397,
    39223935781392739568679612017532185385335838825690788925289597208327612882695725118502311733484217270705030162612162514512780431377563955,
    223597574134938068655085984785795608367622397002907030526855169292325334907200688875395037377056206536281216218951782578692949125062711013692553,
    70117605539022430916500038211073938964246703099663132292782870140044891644079154083694725990919094633480628202430228740733258277018308611945503,
    1318869216749269362521714581530011875926419222618906198033234333354125738673225450909301352359424066159005864397430822759955978123436777013248,
    496919781528258634238871226419881650157979480835145808100115071576040955643771719238489074474620625602922374184204886358833521764964601746740253,
    84617087926536529771024445467064666256331285871866548307663134614693570446407854013907276524052026191232495894182491004253493621263943123,
    216482177690202581336562988489084950290802706055176061507931935641669727977410256034291854508900158649574224848160191501218226984924078832630795,
    34162582983938379371898573211740404495431472771298428626085024283338325052262836155162972342704996027965184764167694850439807312222418434534413,
    217362849645556646804543980432643281601290464958520885910784741908932860039054940484246509133342691271757525872484761214589849987881970434065,
    326248946081522161357905679651977955198337986424559990092592442051907090138520895871560254698208088578142107795453544915596871503000281246006272,
    48347092984486368452536698563890629794074450871448853506997328958663439149837538435259004551749732553266677754166288526953481832256535,
    1277532449012430142489032229733457034693582785611510917721928226251979354555604673970279067507589742052732601981133129344896571743108422383498307,
    38810311753839705115860679886003965187240565716925131855598776985295946154447662064000972346623659730162174332929701134414113768086247064576,
    51894415485507443713386065387323392937812056273849052856016647898997987763232052285359809004328225024251979818785778470443528118773435203693568,
    94634076279570032084768754906720461510500530762662400429536510152133616080062615053325158667254847271361121570153676006499481432845871647695872,
    125995228064401640440263167547649085814078073497318764210942374390788258593342741256266324094949235363408577389902426953170189924562155156288512,
    132378148355329885706762388015793586077003029896805049420305251218043466280398955578380099464317772466444103159034910178012846647125854638833664]⟩,
  ⟨269548, 1155, 356, [
    132378148355329885706762388015793586077003029896805049420305251218043466280398955578380099464317772466444103159034910178012846647125854638833664,
    643283970202891821819425106717147377677850606809317625909947569034190649426546804353386904712692683756393111693673651345743254936819294599643147,
    33781510245106130702604727876737274451482099520546907827757197120882520576300046316293763666162798394813359851837705121054699551030976831303077,
    332295531965711635885082641765614438314923340517835529052107299731786530673344125717287514764289693729208533306505172239245307671967798413754368,
    39631745349666496367722251034497763067711177382112096948503723472371925926182416151743801626959689322927337011212817668020383797174918631653389,
    1246534282354757239139313476833918161658627582383893768428288235575418314235434685367338307294688123825807073728537802938109522132074496,
    509113288967549514297618273808877046867303216143762219954704073480296256595663351711442921098735138259374964206976994185914974589389316375469056,
    31231430055365648281023552760728034320456894789360587244383371157289335804418687280303814854799861957594936752885603160556018636685312,
    88799111048787232496204017402471470679726402004760292332096861173262068314408585206440026442763626999513699614870521313986976929186517468840025,
    70156101875800525372062073098479970221994054951989381203937239581560827181617768231077674317518755714226085103526136865893450231003062277767185,
    57973717834355077176302782189228153649502386876330474734866807530555906529276871995497648710568738719417885642394521117624001280145794840657963,
    48485674941090689481488437381882983575530291087887657967978464393315175040529417575848746331361348133954694249566079465667853682737152,
    32885128151855513624297201461172676607923614277090540670292133987666845796053411006029737012948504826376262901688765689364985171271290467339,
    34216238218515973063112098682067754351012480295364492330911734467674651671437645455941274635207318844656458692264476627649556252916122601401344,
    52323116716705635920676909198734541075430989818123286418573220355095486227700958160422433522835727252518018116309607448552535733622295919361024,
    1028621171215186739617322904152118968392625752474536155697962675531697633777217649070695125853800001033949073074318985751183997055773531813506397,
    1185898668636870144687685654690668650789376093923288947028178573635690439369355483479021797268316221567208347285532508503735518666969244129936425,
    39631573392730714572282952677810623418578416464126954372980322716680393284079313088933811000436090638523073010653747108329157525798095872327693,
    84344524022311495880407786919144429958705093294615570551662907068145747887589342184376403768862577262789533399638094384156259645474753903,
    1218181815780338639172996634311015095307262773809976000292596933482042106466606997702262865362222996406093854318597481115293554488074305536,
    143340175905341132912687568213876640678866289016238685070332192833175445847745092344991872958423646570804034689472844727662772479615979425366016]⟩,
  ⟨273869, 1157, 336, [
    143340175905341132912687568213876640678866289016238685070332192833175445847745092344991872958423646570804034689472844727662772479615979425366016,
    1369257605159614081076458562228175268547643761365646208072326327182639255966194746163524071930777192948839547260774624794887981661522764722339840,
    38758013522208338282861830081474462429070798907761725757691385448354745992972190894227318063680327206159892210829345982528353522727886689280,
    32786613193080612209600222923719619595539030350144468020073828515387621921892223160602034634628268798298574482099364152630057487853737213963,
    34068207336534987830875676555854417279867407687176024200431406259387155041817911114870132926190324171191988992762653491549113191825173501717504,
    32017960599550598815117709368469652877968252872586685878679580703341452064586914534591413153895266748095710612713146555069903841246852293,
    86456066558720368579996479568006016828612594834960329254448459633213065267166820839591937804227234977681893024118191662959526303462962757649,
    50612424160698616995772321203137504896716786389125566128150576411460202838729315831356691704344305562987954559968021289861230278598199487549,
    552082380814257207566655439284970368127765911896419480927309396525269411317861665415295014964402785313082751244851853383110278820687861131539475,
    58062994012583388295994317665530483245113386464767558112583971304843616489131422039641112571123123848589633199655423676788179306372331777055781,
    39632390359861665007231723345620252511194557054300800771902144439795101009568452916344398405119592827181488351325866741292346668250081109492749,
    51826464869218194624937602580151654939288065899386823183180545591938960869116058534322763292787540374625511218831750301362697754974047661534647,
    70209815371064073471876271355184497161827750698530520683352462326828202311456561323292048995870172340694038808545391663730149854355848833711255,
    49425033252101343442600509950642314418160973192941784223057030984386910241762115927569265799689512589774159373368325075719289884854190207,
    112830303486324079731295280786831211748659775337311092494164578447445566602015506779161591380133652585405924992488142562889921382948852453081099,
    33573111080146659496258525653132439237230650500867862813855113307588195558446095492790477653391514005024467750981461062933273195143434077219840,
    31980903947529619503633150394289420703055457420189012714531855531838052942206845482221237383820878571928222534394772909610481334533264437,
    89478350454237519918415733426809368331128894259710491911816767056703082882170842533135748680920537884153703868624954034150910536422716452391936,
    241948786622276075038837763041464492320284426035806572271724125441681413768048104916656241452264788605523600831960464416025766586145113822475311,
    56565496916760537069066710123489119339888334505095442794948761225026757413882856299581277682582487357853000543454075252732369401004377111623,
    125173490362915587296615455361606843437591995347755344206789593260676191946272139088507686025567763837053723645613994842108596329867135686803479,
    545824351682387634207401846120445574661114154394024100649564688381256994403514956381547731008005679044668926502088581375502454586802824054625531]⟩,
  ⟨278291, 1158, 358, [
    545824351682387634207401846120445574661114154394024100649564688381256994403514956381547731008005679044668926502088581375502454586802824054625531,
    122466510364514940060157041630905046492789155881296361492668936506648707952843742604384927363813921614224478885584482675744828647529482551375,
    39700047415222279534961594576731732166164733316819497230822811606337176995463663408590660563408978961129215077139668425675318177543140492181517,
    50612224936993752351067181676360052576016405358016636557680610496395443608517094982294149888670032149173793667925862045100923159044749872128,
    32838621830309554603733243957992943549521259904997503832697498573145183560144879406971612127591616740205296804448896810555004149656539134987,
    34245942663849842375734488606449337297534721382971793808766390900204690559728012279133863346846261283056985706497591446962966105676294659255325,
    32154148651826288319236191231368719277589581062257111530451540153136276967557649723894868100613394930453244113960323921225779200236995603,
    51865004683486854982169960217011657469451371906889344376355182088428736863294685152225982202357629931446712293878159210957523166603702882533407,
    38627503456852261451150175111123894023037951251681706260996246463985879996385874239817710675086714762593016165856742295199853024417677312,
    49425033252101364254456954513289157245752999517624365771270839854736192394691019402869853802701057463745430593673947519105861025461698663,
    827538333722479540155509048163736661538632360464432541539731788558270945067698713994406369100093463717065445931958850891516287519517260790117376,
    306644535751669735303874575951422488440732778558959762121154177610609539454504997616069866294060020827795785719727023120627867078373919448064,
    589409500353853304526870247461109901704214031317037655874747312407656883749979003940001660415073640413089906049160026883460241029880599659151403,
    175650753753794010249231873068357620942205443742311037782154760684173182463310414147421271625139305868964499195413137072391992219472967500009,
    70203736381704412149611400889534867766833414681250287041302360166396915951578541758221236642274102191366680971330269998921882386408443793679360,
    39664638740131555843268313150510486078167704425107286464063951534408806714131067908785424416650223487028508109991093022475727467045393979689995,
    34895163856824374198817209755585142986441668048718091476768406856620578307782618846409992552490203098789138288041003566605013607003280266767401,
    222603124990544615485200285668815734807328971693170330965581500972181369444862456187015666970767090313389697189984711928695991871650984052654080,
    1092674099342747767381518176927854580146956925856558365770150272711002106933279008151204846664224158005697084486030872046244891868416055764195,
    94506114950900721685680006967674908819604492451037990888202539968485254594822121727919906092624841866190537659521025975446854058966742757127185,
    216488065083880306645530402478294741401232926734726569456923577959355046154918026244149854553869461775203766897983294271497538175766737676402688,
    914017172224392795345627296170564231551472743991445461674852498101417512403147320736810043764851794215847059919747956128791896528799262572611]⟩,
  ⟨282791, 1159, 364, [
    914017172224392795345627296170564231551472743991445461674852498101417512403147320736810043764851794215847059919747956128791896528799262572611,
    582371733413603043398328196685622522114625832688102927506253065338780788679065940267660812357613585862517690655070418532444881852549265307755543,
    110153899285893207541912454664050635568412291791071210854527785106597543608322254698801790248849674848699565514608882698559503918008642843648,
    52043667456545324487872481485791984847248549829384073528471775430155091276448210137919937210294505488172520555472164430500805951876372649476096,
    88478436027107811583035063033240197455273423354841391572782801677076878474677383039237410686687970310789676461935048456224460433958668665429011,
    57955867462494473816650054297782247976396592366011597004085169356040346124794008398168308340054844057082214578920852985444618457073929507831819,
    33534408320696655631918897473079446596443530968007547051247327819778937308455991382969402575319171927492357920265453378490370646087606130977792,
    39631605374466411738673822159144448898971593325662125653633249962556578944524274869930409561756783528236169442638355951869598522433881232113677,
    108631157982239091802302945417543463446013765838551431488425666411473437014455430713102634732551537426884161005000257661582072051194134685,
    112797555129276405747914413217198102529744903074280277025462516696351621390608696987039421435442940123990155323341053932461621212700626984027593,
    478627463414312949762599791073164874697143408126013899620462021028015700762175669853672051967367440096699795393583576890154041681087270504344576,
    648371373539687522097097392485368201112766924039071535904325138305792115115609300670667497313715200552131711866242972933178886245399434240,
    38702708920872416371541442742040223483106111368770690988969298647383544391172487865860697245738489259026384031723002406675754399278593797120,
    943789814092150680680268668030825846478193439178576708622502459711593730100158416631455705136203731811025336423150817596144931211552060623901,
    1338467757251426472917989305989257078524211646283027102680207118000020788834581071748713952975261698071819109647895909913341690121818099722255360,
    57667421564863962415164461627449916365469141559173974061366993426988577953080158071807432030785886549476075352384389072514691798707756610577,
    70150147524961014329680817808796764569711948595439804219167781649624027816817349792565063396880222870735518991140418732693626286627772897951755,
    33534463543357283084149562371618117887790816158879036282733046842399865969917967901347761294020311357134321632565515752509913285712002620075039,
    33022895357252135695182829366214164127670852408647901172716102306572655460415259412855029929912298348890107803650081325783866587372151947,
    124992039572789978076828954591828369048799828099748889425859201596709258729748331956888828315379055937797825252741086141771069993134302070588416,
    39789428332373527776100658819954372560583448759819555305928172544440636112420432463050804542226206259049770140399615494055101190586696043855885,
    122239790597096770333863841149965634400706318189395238180459070127146579686459733524413040901937527946856815135024984763784876807860461240320]⟩,
  ⟨287364, 1161, 362, [
    122239790597096770333863841149965634400706318189395238180459070127146579686459733524413040901937527946856815135024984763784876807860461240320,
    86386267355318214865428598711353592120513979702767288734651903029418680907376812948990543204767310307726758680229176692892669699998079779007,
    247102557648416889960225067340328364694878960924306208678368520197451445332171572430275333864800651432293035709011239676323391702028446206995,
    57923069364047055623635372488291425731265603936301038400754284016495636530548001566787774994147801798383184257396619453745813098212722596672535,
    161613579527382894259106757953440533822240520299656034946962884837788658106525413538500356187580767743852989477126644138058249373976216539758592,
    295712547504476940482933616004112191965818815647360569554422203836612854585763913715462647611451822480317669868147357512268254260189201804820541,
    32748527899113660721595934330564392999438667678376969109998329548826624104682611212328007436776813129575607799154063352710433059463868435467,
    34520295245410427432475852267495301752159981182687402312945670416638903187696248379331123439330084400587002454032882275066205496074843385244672,
    94506091674948626415951663793933076950131445430478613410764990139055017723641040467203686394600034598861747052689002263564913915462250877080576,
    248780502823618087105066172297872462782330990674198377304125204089955114538962234325327612970829767532831565694369792,
    693671844112241685077847033061214716480306863046699307201405774335546981042642203766409756581554655847056807701602929642487297351367167016099,
    92870179770606261539073524449368917740714013486456686924481846875661500039574956694013152807063479714028435396363458581551353127034407635985,
    39682184658345230426316159179648491979315566600350375209398216545269296558694156908490214112731994912846631803558363248951320488122058533765133,
    57370883415807104179045010479640711454185617264250036675827466572400125765848337281943528405795166012424713399202368861888650627489477993515,
    948648351373305370665772155026705057251173475482725702000247423403857842663046098830026567251082667743331598394184056031208750749212925675700313,
    55560574202157211621406542809208458782822036631051416887590322015634096747733452835231957273887073647366302483480823069330737951311676457,
    52400720941248406914501612185741080660575298522252142273038821185330479020376831256748784098639060625070567503117681540303560157233929769819365,
    326231083415119999510091816685783204681853512958658775254496793218403016237262308657655160211943344335635023019983658230135335953926796779656203,
    33644599913419394398467201097563721723951647679920323720791276296119010302747092864577255725622926501518607323642609461085291328728982028823649,
    235225416659545587237955651081625163463271288701108957393852484243268585756886376003630311581192301179399415617008500051018330777218456925184,
    783485720184994471209836813539191408456587308280651251669486102539662854390542294348787779401141915491412706275455079592015657005024613335315493,
    299693245197138822699446811788089144155228350835968701226433847565011275705937656900677771371011183784297410487790991899567767677071109139,
    58134512297816661002719316789671538165847959827594001406821680021837663283334623217552955207787612176562449314069218570029566306256819497992192]⟩,
  ⟨292039, 1162, 364, [
    58134512297816661002719316789671538165847959827594001406821680021837663283334623217552955207787612176562449314069218570029566306256819497992192,
    527404921056468835486917634526686237154018241514869673826078124705521814695463290360271206429612699857349619890444645098518262400667662728298496,
    387369544786827213829847176748209187451275794603918653775705277070525428934896026331625269862819331376082892060238339130094281625757320922299392,
    39631692767456870463064494497183673396601244373798024569798614455178667023509983324270685479801358861932732885986030481639411064610143282921485,
    1138315127811085092499711143637736571365278623212286347495690118776774030840273208059710677523730043578996496419364202603230136548898808012022807,
    309554792633825776262046108730813052088219540366642402088703729922236724115269373284297141912739712477034593260749704876588819889034271,
    606701182582883831752285957834375156946821347783927127096335376769244026250297933415205826429482686750297681956529970885034072722654634603184139,
    33585020293208561955679943234785978693804778702285397164716363745597348164114107658556156933265919908411599418861531046632798895871462384610304,
    38734737562334347030717229174202080146910122313050457434818177466311393787266789142906028839391361926489259410903132804788514566352089926757,
    143283418588309800770934991889385225028338884032598998688545495767932569398345674839411529911088182139762292209540314164329752142929385170665472,
    56565496965661377326353233828998554455224756407000747276844112592633539462055153307484178344574197751478792665351567741077812549638473925632,
    51826476453681779176607726067145390969991729766272868969101393171218149207430163713580845382813925426725933965381794347419326679260938075386953,
    240838078195779375601845781666517513499413248876226864190477400493577391355819197400688796151897309167651422841783907504048851574098868026012851,
    49507371862070981033023223878410707877015794940947636683699448090742938709173006241781045661177198618510961504510405087397232330418421760,
    241415537910472870008308028439351646287954217345211867554997935707028739712665067212966406862012406080913259799394894753658527322259053627,
    1552213799872590745549712900626006554376101540830541506532025996647606997566926530306211817140792212516316601644962806215024719765300288862290279,
    39631573447562946380738973841705191014108718963565471682698749642346453338948675980955011838061536320751099562787076581268396649861717580340237,
    94538979608207592729061375405243988298229987895444050632822489077277614939493521003044080984069225238577080090848739190827445508456533403369483,
    33674333431891879780756798957715796822628391453512972049202148216729784476554275142445599380615836069271064628603259634281045160161795873188883,
    58045164261635617171863660315896465415478348511933072043258318042302195921388011872693700408530158301416003950462820117708288220976457343732736,
    92291462931745929394935841556214039226650894870435937124733620842255516019950798783695013652176288501597918110841274057833382759413194948608,
    38703137309430947871318265940150331972593553444543787389898021439884410534824826430238675623284520249708148683116173171311418939113802301440,
    179994425997856160112053750725660533857320815813844852888818492218227661454931532840887777684157579753050647659370648671264416806368957827206144]⟩,
  ⟨296799, 1164, 371, [
    179994425997856160112053750725660533857320815813844852888818492218227661454931532840887777684157579753050647659370648671264416806368957827206144,
    66900394633843973465173937036827689629036032485775545308960206197104702684085900624488214789741835123644288657123855500666852606200812561,
    131139661723884809120881553403351103994709020696382755539555579755579127652851006325451750865331153054161191407696857921173925951835315475854403,
    186555985888571010731778843827172990618177487415980268716330464632562985502775048994119601604689034651980349716825414008125279024734622824005632,
    223134351062794991573607291482419819738610191664965404361571510479471477024956414684997246871033213388819962811718284144537358263915976746769491,
    216449362527104173467299173475902250974681045211889287777501755281035669104145394552697383193701158362382961352891147981903128289129668673553431,
    51858652200933460353931357816825651057284477717979504933414518582603456542171919438950857859871988171008024308524754553199571294452248255458315,
    33591058528430271951927187708234430759460679162527424535886789784366631478608199364822655336727577149354671177130146934894443272112274523827213,
    271392354615620065252440826409476717587493152895827888188535404228558620411786116345972607318406460201429196980885627102607958098316310588040365,
    55239790585489087682450244183574205656278367856510852124434364352421498656784205445074208525818418386232798591609088135252454657300184064,
    728611428770025067106196737138086967545332609718844867778799832527258189088067088174546082963116052921288377320972023588664942263844540677923840,
    692138487078203576160487052342044964464348767864920423517761712187288827412552657065505555928541106236653334884405206327420369293096126941002752,
    38996382547729432809671234528057166608976611028220763764516458686109170681060321140012260618058006042733032822504470885507405376484463869993,
    161574913988960972601197713098745101456438998328953806511997683267869099524022610880776674399672171742745691534923699000337127991064561198301221,
    30583365816584886963201678607185339311841622829822667788906628129861146358411105472679741278591019152060671118885123458579764915231,
    86336847989189280710673463239508756979420221694533953316761324279516157068565051425800362535265958338399097891035826081241710112119324685331,
    57924112667222775948583293541600506237975095151172710977513117634211870850703636188849690852448764880739601887992705075415564171962142189158903,
    1393235089899703172339677307299966545480494682947230784324931893916894893010935393620386255945278474192872188172652960160311138878992282853334027,
    33534408255347602583075441078864134951372675915391686450522029225190652734023552573746611377741118738712596629047511032288151679440288061860881,
    50643215040024912520052496593794363894397534626190113022472546295148424515110321877263737115695467354206733304257917207013629466393784091073,
    39632099672538648466094854743877180585337034513262267238753232698949921036776523199625628875089832748103188315980375607397673605165595772359693,
    1328154848508027236433792087720519282500370440746768528206747871310292372162772064686924152090351874797962776729636333077996657444039,
    119201681828367470860419544968199563405201495732785954225415956408238615420376741096075809742565300411255183626916564209334054939092075581,
    51826668332924912837291761809302846008267752298304651993806294945184884485226714287052300410232708941963922128231433654143085783006482749456384]⟩,
  ⟨300000, 1165, 240, [
    51826668332924912837291761809302846008267752298304651993806294945184884485226714287052300410232708941963922128231433654143085783006482749456384,
    497237578623584032958446108946168973210214764688357743181074407184780750526170012021605362905536676124820970583729201091318836713677516130241536,
    38753294693553129816040400396724980406058827463935498510666498450766987385789031601338780251207061175255924924563997384202169577704120123392,
    88465498206954287088529256290553685339179960692523397825177169237100495861300198721421848865858474252485965270711329159128421837382341329158247,
    568844709518061725540422845522860055443729095560155560173020130335883194632899495886344740891865042213077547417661654751554746272273721721169,
    32803722214688396200741286717828218372908109789086842804275556455055644305434690243390855419356721573927664974950628858163037114963698136075,
    33626699434290715639989669107454258897833662000349973368386440461818379974426276558739216877084750604335970782480241085491016470623261719276544,
    32489409338375430222481516719723217072451974819650663401648728909403616176193875526841390752203265035910507381255187894096122206322950144,
    204323506239699638247825510034095798625279752754191565647754820132072409856654973358111557957940113936490429409815035320589924157474692098630656,
    460335967923170533411457347415025822628350611565561135477762737936635958432071618352654502175888083528503682009012737534647103601655245798637568,
    39631573458171180630667229400112589242996451829942176390549984200481933169527680403220201004632059311600938141715051657620293461242701583220749,
    143283505774938983381197678650500620398667646661613350427295352217071771380969560259973617183438321714476436287751885338356463277180254523851795,
    58104674533734171807229953374899155138341022873093728055034770090178217790011110878268679466784234435255912169232121701491540906751623689142289,
    125042580862759291253579603317100416624774451385942715025045741516311339249424546691544294331327597972190498149977734434226006431727291478311259,
    253333703490155266462413067560544977107869833166738641340813396090728961210744160999308972192112778828239327594127270676532716677976764060794880,
    39019610355171535271981259860749447152662515386716191247631113510983549273894996433939853304700155100500232649425272888026592596787895205888]⟩
]

set_option maxRecDepth 10000 in
private def analyticRankIntervals : List NumericRankInterval := [
  ⟨300060, 1165, 1164⟩, ⟨300121, 1165, 1164⟩, ⟨300182, 1165, 1164⟩, ⟨300243, 1165, 1164⟩,
  ⟨300306, 1165, 1164⟩, ⟨300370, 1165, 1164⟩, ⟨300434, 1165, 1164⟩, ⟨300499, 1165, 1164⟩,
  ⟨300564, 1165, 1164⟩, ⟨300630, 1165, 1164⟩, ⟨300697, 1165, 1164⟩, ⟨300765, 1165, 1164⟩,
  ⟨300833, 1165, 1164⟩, ⟨300902, 1165, 1164⟩, ⟨300971, 1165, 1164⟩, ⟨301041, 1165, 1164⟩,
  ⟨301112, 1165, 1164⟩, ⟨301183, 1165, 1164⟩, ⟨301254, 1165, 1164⟩, ⟨301321, 1165, 1164⟩,
  ⟨301389, 1165, 1164⟩, ⟨301458, 1165, 1164⟩, ⟨301528, 1165, 1164⟩, ⟨301598, 1165, 1164⟩,
  ⟨301670, 1165, 1164⟩, ⟨301742, 1165, 1164⟩, ⟨301788, 1166, 1164⟩, ⟨301865, 1166, 1165⟩,
  ⟨301943, 1166, 1165⟩, ⟨302023, 1166, 1165⟩, ⟨302103, 1166, 1165⟩, ⟨302184, 1166, 1165⟩,
  ⟨302265, 1166, 1165⟩, ⟨302347, 1166, 1165⟩, ⟨302430, 1166, 1165⟩, ⟨302510, 1166, 1165⟩,
  ⟨302592, 1166, 1165⟩, ⟨302662, 1166, 1165⟩, ⟨302732, 1166, 1165⟩, ⟨302804, 1166, 1165⟩,
  ⟨302876, 1166, 1165⟩, ⟨302949, 1166, 1165⟩, ⟨303022, 1166, 1165⟩, ⟨303096, 1166, 1165⟩,
  ⟨303171, 1166, 1165⟩, ⟨303247, 1166, 1165⟩, ⟨303324, 1166, 1165⟩, ⟨303402, 1166, 1165⟩,
  ⟨303480, 1166, 1165⟩, ⟨303558, 1166, 1165⟩, ⟨303637, 1166, 1165⟩, ⟨303716, 1166, 1165⟩,
  ⟨303797, 1166, 1165⟩, ⟨303878, 1166, 1165⟩, ⟨303961, 1166, 1165⟩, ⟨304044, 1166, 1165⟩,
  ⟨304128, 1166, 1165⟩, ⟨304213, 1166, 1165⟩, ⟨304299, 1166, 1165⟩, ⟨304386, 1166, 1165⟩,
  ⟨304474, 1166, 1165⟩, ⟨304558, 1166, 1165⟩, ⟨304642, 1166, 1165⟩, ⟨304727, 1166, 1165⟩,
  ⟨304813, 1166, 1165⟩, ⟨304900, 1166, 1165⟩, ⟨304987, 1166, 1165⟩, ⟨305064, 1166, 1165⟩,
  ⟨305158, 1167, 1166⟩, ⟨305253, 1167, 1166⟩, ⟨305349, 1167, 1166⟩, ⟨305446, 1167, 1166⟩,
  ⟨305544, 1167, 1166⟩, ⟨305643, 1167, 1166⟩, ⟨305743, 1167, 1166⟩, ⟨305844, 1167, 1166⟩,
  ⟨305945, 1167, 1166⟩, ⟨306047, 1167, 1166⟩, ⟨306150, 1167, 1166⟩, ⟨306255, 1167, 1166⟩,
  ⟨306361, 1167, 1166⟩, ⟨306468, 1167, 1166⟩, ⟨306576, 1167, 1166⟩, ⟨306684, 1167, 1166⟩,
  ⟨306794, 1167, 1166⟩, ⟨306905, 1167, 1166⟩, ⟨307006, 1167, 1166⟩, ⟨307107, 1167, 1166⟩,
  ⟨307210, 1167, 1166⟩, ⟨307312, 1167, 1166⟩, ⟨307416, 1167, 1166⟩, ⟨307521, 1167, 1166⟩,
  ⟨307627, 1167, 1166⟩, ⟨307734, 1167, 1166⟩, ⟨307837, 1167, 1166⟩, ⟨307942, 1167, 1166⟩,
  ⟨308048, 1167, 1166⟩, ⟨308155, 1167, 1166⟩, ⟨308262, 1167, 1166⟩, ⟨308370, 1167, 1166⟩,
  ⟨308453, 1168, 1166⟩, ⟨308568, 1168, 1167⟩, ⟨308684, 1168, 1167⟩, ⟨308801, 1168, 1167⟩,
  ⟨308919, 1168, 1167⟩, ⟨309038, 1168, 1167⟩, ⟨309158, 1168, 1167⟩, ⟨309274, 1168, 1167⟩,
  ⟨309391, 1168, 1167⟩, ⟨309509, 1168, 1167⟩, ⟨309627, 1168, 1167⟩, ⟨309747, 1168, 1167⟩,
  ⟨309868, 1168, 1167⟩, ⟨309990, 1168, 1167⟩, ⟨310113, 1168, 1167⟩, ⟨310236, 1168, 1167⟩,
  ⟨310361, 1168, 1167⟩, ⟨310487, 1168, 1167⟩, ⟨310615, 1168, 1167⟩, ⟨310744, 1168, 1167⟩,
  ⟨310875, 1168, 1167⟩, ⟨311007, 1168, 1167⟩, ⟨311140, 1168, 1167⟩, ⟨311271, 1168, 1167⟩,
  ⟨311401, 1168, 1167⟩, ⟨311520, 1168, 1167⟩, ⟨311641, 1168, 1167⟩, ⟨311744, 1168, 1167⟩,
  ⟨311873, 1169, 1168⟩, ⟨312002, 1169, 1168⟩, ⟨312133, 1169, 1168⟩, ⟨312265, 1169, 1168⟩,
  ⟨312398, 1169, 1168⟩, ⟨312533, 1169, 1168⟩, ⟨312669, 1169, 1168⟩, ⟨312805, 1169, 1168⟩,
  ⟨312942, 1169, 1168⟩, ⟨313081, 1169, 1168⟩, ⟨313221, 1169, 1168⟩, ⟨313363, 1169, 1168⟩,
  ⟨313507, 1169, 1168⟩, ⟨313652, 1169, 1168⟩, ⟨313799, 1169, 1168⟩, ⟨313947, 1169, 1168⟩,
  ⟨314097, 1169, 1168⟩, ⟨314248, 1169, 1168⟩, ⟨314399, 1169, 1168⟩, ⟨314548, 1169, 1168⟩,
  ⟨314698, 1169, 1168⟩, ⟨314850, 1169, 1168⟩, ⟨315003, 1169, 1168⟩, ⟨315139, 1169, 1168⟩,
  ⟨315300, 1170, 1169⟩, ⟨315463, 1170, 1169⟩, ⟨315627, 1170, 1169⟩, ⟨315792, 1170, 1169⟩,
  ⟨315959, 1170, 1169⟩, ⟨316113, 1170, 1169⟩, ⟨316268, 1170, 1169⟩, ⟨316424, 1170, 1169⟩,
  ⟨316583, 1170, 1169⟩, ⟨316743, 1170, 1169⟩, ⟨316905, 1170, 1169⟩, ⟨317067, 1170, 1169⟩,
  ⟨317231, 1170, 1169⟩, ⟨317397, 1170, 1169⟩, ⟨317564, 1170, 1169⟩, ⟨317733, 1170, 1169⟩,
  ⟨317904, 1170, 1169⟩, ⟨318072, 1170, 1169⟩, ⟨318241, 1170, 1169⟩, ⟨318412, 1170, 1169⟩,
  ⟨318570, 1170, 1169⟩, ⟨318748, 1171, 1170⟩, ⟨318927, 1171, 1170⟩, ⟨319109, 1171, 1170⟩,
  ⟨319293, 1171, 1170⟩, ⟨319478, 1171, 1170⟩, ⟨319666, 1171, 1170⟩, ⟨319855, 1171, 1170⟩,
  ⟨320045, 1171, 1170⟩, ⟨320237, 1171, 1170⟩, ⟨320431, 1171, 1170⟩, ⟨320615, 1171, 1170⟩,
  ⟨320801, 1171, 1170⟩, ⟨320988, 1171, 1170⟩, ⟨321178, 1171, 1170⟩, ⟨321370, 1171, 1170⟩,
  ⟨321557, 1171, 1170⟩, ⟨321747, 1171, 1170⟩, ⟨321939, 1171, 1170⟩, ⟨322105, 1172, 1170⟩,
  ⟨322302, 1172, 1171⟩, ⟨322501, 1172, 1171⟩, ⟨322693, 1172, 1171⟩, ⟨322883, 1172, 1171⟩,
  ⟨323074, 1172, 1171⟩, ⟨323267, 1172, 1171⟩, ⟨323462, 1172, 1171⟩, ⟨323659, 1172, 1171⟩,
  ⟨323858, 1172, 1171⟩, ⟨324060, 1172, 1171⟩, ⟨324264, 1172, 1171⟩, ⟨324470, 1172, 1171⟩,
  ⟨324676, 1172, 1171⟩, ⟨324885, 1172, 1171⟩, ⟨325096, 1172, 1171⟩, ⟨325291, 1172, 1171⟩,
  ⟨325488, 1172, 1171⟩, ⟨325660, 1173, 1171⟩, ⟨325866, 1173, 1172⟩, ⟨326075, 1173, 1172⟩,
  ⟨326284, 1173, 1172⟩, ⟨326495, 1173, 1172⟩, ⟨326708, 1173, 1172⟩, ⟨326923, 1173, 1172⟩,
  ⟨327141, 1173, 1172⟩, ⟨327361, 1173, 1172⟩, ⟨327583, 1173, 1172⟩, ⟨327807, 1173, 1172⟩,
  ⟨328033, 1173, 1172⟩, ⟨328261, 1173, 1172⟩, ⟨328492, 1173, 1172⟩, ⟨328725, 1173, 1172⟩,
  ⟨328955, 1173, 1172⟩, ⟨329160, 1174, 1172⟩, ⟨329399, 1174, 1173⟩, ⟨329638, 1174, 1173⟩,
  ⟨329878, 1174, 1173⟩, ⟨330107, 1174, 1173⟩, ⟨330339, 1174, 1173⟩, ⟨330573, 1174, 1173⟩,
  ⟨330810, 1174, 1173⟩, ⟨331049, 1174, 1173⟩, ⟨331291, 1174, 1173⟩, ⟨331534, 1174, 1173⟩,
  ⟨331780, 1174, 1173⟩, ⟨332028, 1174, 1173⟩, ⟨332279, 1174, 1173⟩, ⟨332528, 1174, 1173⟩,
  ⟨332750, 1175, 1173⟩, ⟨333008, 1175, 1174⟩, ⟨333267, 1175, 1174⟩, ⟨333529, 1175, 1174⟩,
  ⟨333794, 1175, 1174⟩, ⟨334061, 1175, 1174⟩, ⟨334331, 1175, 1174⟩, ⟨334604, 1175, 1174⟩,
  ⟨334881, 1175, 1174⟩, ⟨335146, 1175, 1174⟩, ⟨335414, 1175, 1174⟩, ⟨335685, 1175, 1174⟩,
  ⟨335959, 1175, 1174⟩, ⟨336226, 1175, 1174⟩, ⟨336465, 1176, 1174⟩, ⟨336738, 1176, 1175⟩,
  ⟨337015, 1176, 1175⟩, ⟨337294, 1176, 1175⟩, ⟨337576, 1176, 1175⟩, ⟨337861, 1176, 1175⟩,
  ⟨338149, 1176, 1175⟩, ⟨338440, 1176, 1175⟩, ⟨338732, 1176, 1175⟩, ⟨339028, 1176, 1175⟩,
  ⟨339327, 1176, 1175⟩, ⟨339629, 1176, 1175⟩, ⟨339934, 1176, 1175⟩, ⟨340194, 1177, 1175⟩,
  ⟨340489, 1177, 1176⟩, ⟨340787, 1177, 1176⟩, ⟨341088, 1177, 1176⟩, ⟨341392, 1177, 1176⟩,
  ⟨341700, 1177, 1176⟩, ⟨342011, 1177, 1176⟩, ⟨342323, 1177, 1176⟩, ⟨342638, 1177, 1176⟩,
  ⟨342957, 1177, 1176⟩, ⟨343276, 1177, 1176⟩, ⟨343598, 1177, 1176⟩, ⟨343893, 1178, 1176⟩,
  ⟨344221, 1178, 1177⟩, ⟨344552, 1178, 1177⟩, ⟨344886, 1178, 1177⟩, ⟨345210, 1178, 1177⟩,
  ⟨345537, 1178, 1177⟩, ⟨345867, 1178, 1177⟩, ⟨346200, 1178, 1177⟩, ⟨346537, 1178, 1177⟩,
  ⟨346877, 1178, 1177⟩, ⟨347221, 1178, 1177⟩, ⟨347538, 1179, 1177⟩, ⟨347892, 1179, 1178⟩,
  ⟨348243, 1179, 1178⟩, ⟨348599, 1179, 1178⟩, ⟨348958, 1179, 1178⟩, ⟨349321, 1179, 1178⟩,
  ⟨349683, 1179, 1178⟩, ⟨350043, 1179, 1178⟩, ⟨350393, 1179, 1178⟩, ⟨350747, 1179, 1178⟩,
  ⟨351104, 1179, 1178⟩, ⟨351435, 1180, 1178⟩, ⟨351803, 1180, 1179⟩, ⟨352170, 1180, 1179⟩,
  ⟨352541, 1180, 1179⟩, ⟨352915, 1180, 1179⟩, ⟨353293, 1180, 1179⟩, ⟨353674, 1180, 1179⟩,
  ⟨354059, 1180, 1179⟩, ⟨354448, 1180, 1179⟩, ⟨354841, 1180, 1179⟩, ⟨355207, 1181, 1179⟩,
  ⟨355596, 1181, 1180⟩, ⟨355990, 1181, 1180⟩, ⟨356382, 1181, 1180⟩, ⟨356774, 1181, 1180⟩,
  ⟨357171, 1181, 1180⟩, ⟨357572, 1181, 1180⟩, ⟨357975, 1181, 1180⟩, ⟨358383, 1181, 1180⟩,
  ⟨358795, 1181, 1180⟩, ⟨359180, 1182, 1180⟩, ⟨359605, 1182, 1181⟩, ⟨360034, 1182, 1181⟩,
  ⟨360461, 1182, 1181⟩, ⟨360892, 1182, 1181⟩, ⟨361314, 1182, 1181⟩, ⟨361740, 1182, 1181⟩,
  ⟨362169, 1182, 1181⟩, ⟨362602, 1182, 1181⟩, ⟨363009, 1183, 1181⟩, ⟨363450, 1183, 1182⟩,
  ⟨363896, 1183, 1182⟩, ⟨364345, 1183, 1182⟩, ⟨364793, 1183, 1182⟩, ⟨365245, 1183, 1182⟩,
  ⟨365702, 1183, 1182⟩, ⟨366164, 1183, 1182⟩, ⟨366614, 1183, 1182⟩, ⟨367039, 1184, 1182⟩,
  ⟨367504, 1184, 1183⟩, ⟨367973, 1184, 1183⟩, ⟨368448, 1184, 1183⟩, ⟨368919, 1184, 1183⟩,
  ⟨369395, 1184, 1183⟩, ⟨369876, 1184, 1183⟩, ⟨370360, 1184, 1183⟩, ⟨370817, 1185, 1183⟩,
  ⟨371314, 1185, 1184⟩, ⟨371815, 1185, 1184⟩, ⟨372307, 1185, 1184⟩, ⟨372804, 1185, 1184⟩,
  ⟨373300, 1185, 1184⟩, ⟨373799, 1185, 1184⟩, ⟨374304, 1185, 1184⟩, ⟨374782, 1186, 1184⟩,
  ⟨375302, 1186, 1185⟩, ⟨375828, 1186, 1185⟩, ⟨376358, 1186, 1185⟩, ⟨376882, 1186, 1185⟩,
  ⟨377411, 1186, 1185⟩, ⟨377924, 1186, 1185⟩, ⟨378440, 1186, 1185⟩, ⟨378929, 1187, 1185⟩,
  ⟨379461, 1187, 1186⟩, ⟨379998, 1187, 1186⟩, ⟨380542, 1187, 1186⟩, ⟨381089, 1187, 1186⟩,
  ⟨381642, 1187, 1186⟩, ⟨382200, 1187, 1186⟩, ⟨382758, 1187, 1186⟩, ⟨383289, 1188, 1186⟩,
  ⟨383843, 1188, 1187⟩, ⟨384403, 1188, 1187⟩, ⟨384969, 1188, 1187⟩, ⟨385541, 1188, 1187⟩,
  ⟨386119, 1188, 1187⟩, ⟨386700, 1188, 1187⟩, ⟨387249, 1189, 1187⟩, ⟨387841, 1189, 1188⟩,
  ⟨388440, 1189, 1188⟩, ⟨389043, 1189, 1188⟩, ⟨389637, 1189, 1188⟩, ⟨390238, 1189, 1188⟩,
  ⟨390839, 1189, 1188⟩, ⟨391413, 1190, 1188⟩, ⟨392023, 1190, 1189⟩, ⟨392639, 1190, 1189⟩,
  ⟨393261, 1190, 1189⟩, ⟨393890, 1190, 1189⟩, ⟨394524, 1190, 1189⟩, ⟨395164, 1190, 1189⟩,
  ⟨395762, 1191, 1189⟩, ⟨396399, 1191, 1190⟩, ⟨397042, 1191, 1190⟩, ⟨397687, 1191, 1190⟩,
  ⟨398338, 1191, 1190⟩, ⟨398996, 1191, 1190⟩, ⟨399662, 1191, 1190⟩, ⟨400299, 1192, 1190⟩,
  ⟨400981, 1192, 1191⟩, ⟨401648, 1192, 1191⟩, ⟨402321, 1192, 1191⟩, ⟨403000, 1192, 1191⟩,
  ⟨403686, 1192, 1191⟩, ⟨404336, 1193, 1191⟩, ⟨405033, 1193, 1192⟩, ⟨405735, 1193, 1192⟩,
  ⟨406436, 1193, 1192⟩, ⟨407145, 1193, 1192⟩, ⟨407846, 1193, 1192⟩, ⟨408554, 1193, 1192⟩,
  ⟨409233, 1194, 1192⟩, ⟨409958, 1194, 1193⟩, ⟨410689, 1194, 1193⟩, ⟨411421, 1194, 1193⟩,
  ⟨412158, 1194, 1193⟩, ⟨412903, 1194, 1193⟩, ⟨413621, 1195, 1193⟩, ⟨414369, 1195, 1194⟩,
  ⟨415124, 1195, 1194⟩, ⟨415886, 1195, 1194⟩, ⟨416649, 1195, 1194⟩, ⟨417414, 1195, 1194⟩,
  ⟨418150, 1196, 1194⟩, ⟨418934, 1196, 1195⟩, ⟨419727, 1196, 1195⟩, ⟨420511, 1196, 1195⟩,
  ⟨421301, 1196, 1195⟩, ⟨422093, 1196, 1195⟩, ⟨422857, 1197, 1195⟩, ⟨423670, 1197, 1196⟩,
  ⟨424488, 1197, 1196⟩, ⟨425314, 1197, 1196⟩, ⟨426149, 1197, 1196⟩, ⟨426933, 1198, 1196⟩,
  ⟨427765, 1198, 1197⟩, ⟨428605, 1198, 1197⟩, ⟨429450, 1198, 1197⟩, ⟨430302, 1198, 1197⟩,
  ⟨431148, 1198, 1197⟩, ⟨431967, 1199, 1197⟩, ⟨432829, 1199, 1198⟩, ⟨433683, 1199, 1198⟩,
  ⟨434543, 1199, 1198⟩, ⟨435411, 1199, 1198⟩, ⟨436253, 1200, 1198⟩, ⟨437145, 1200, 1199⟩,
  ⟨438037, 1200, 1199⟩, ⟨438939, 1200, 1199⟩, ⟨439850, 1200, 1199⟩, ⟨440753, 1200, 1199⟩,
  ⟨441626, 1201, 1199⟩, ⟨442551, 1201, 1200⟩, ⟨443485, 1201, 1200⟩, ⟨444419, 1201, 1200⟩,
  ⟨445360, 1201, 1200⟩, ⟨446274, 1202, 1200⟩, ⟨447223, 1202, 1201⟩, ⟨448181, 1202, 1201⟩,
  ⟨449147, 1202, 1201⟩, ⟨450116, 1202, 1201⟩, ⟨451057, 1203, 1201⟩, ⟨452051, 1203, 1202⟩,
  ⟨453052, 1203, 1202⟩, ⟨454065, 1203, 1202⟩, ⟨455069, 1203, 1202⟩, ⟨456038, 1204, 1202⟩,
  ⟨457058, 1204, 1203⟩, ⟨458082, 1204, 1203⟩, ⟨459117, 1204, 1203⟩, ⟨460160, 1204, 1203⟩,
  ⟨461177, 1205, 1203⟩, ⟨462222, 1205, 1204⟩, ⟨463278, 1205, 1204⟩, ⟨464343, 1205, 1204⟩,
  ⟨465405, 1205, 1204⟩, ⟨466497, 1206, 1205⟩, ⟨467592, 1206, 1205⟩, ⟨468679, 1206, 1205⟩,
  ⟨469777, 1206, 1205⟩, ⟨470848, 1207, 1205⟩, ⟨471969, 1207, 1206⟩, ⟨473102, 1207, 1206⟩,
  ⟨474239, 1207, 1206⟩, ⟨475388, 1207, 1206⟩, ⟨476488, 1208, 1206⟩, ⟨477645, 1208, 1207⟩,
  ⟨478814, 1208, 1207⟩, ⟨479984, 1208, 1207⟩, ⟨481127, 1209, 1207⟩, ⟨482327, 1209, 1208⟩,
  ⟨483539, 1209, 1208⟩, ⟨484740, 1209, 1208⟩, ⟨485945, 1209, 1208⟩, ⟨487113, 1210, 1208⟩,
  ⟨488336, 1210, 1209⟩, ⟨489571, 1210, 1209⟩, ⟨490819, 1210, 1209⟩, ⟨492020, 1211, 1209⟩,
  ⟨493268, 1211, 1210⟩, ⟨494528, 1211, 1210⟩, ⟨495801, 1211, 1210⟩, ⟨497043, 1212, 1210⟩,
  ⟨498344, 1212, 1211⟩, ⟨499636, 1212, 1211⟩, ⟨500932, 1212, 1211⟩, ⟨502198, 1213, 1211⟩,
  ⟨503523, 1213, 1212⟩, ⟨504861, 1213, 1212⟩, ⟨506209, 1213, 1212⟩, ⟨507527, 1213, 1212⟩,
  ⟨508881, 1214, 1213⟩, ⟨510248, 1214, 1213⟩, ⟨511626, 1214, 1213⟩, ⟨513013, 1214, 1213⟩,
  ⟨514362, 1215, 1213⟩, ⟨515749, 1215, 1214⟩, ⟨517150, 1215, 1214⟩, ⟨518566, 1215, 1214⟩,
  ⟨519955, 1216, 1214⟩, ⟨521392, 1216, 1215⟩, ⟨522844, 1216, 1215⟩, ⟨524289, 1216, 1215⟩,
  ⟨525734, 1217, 1216⟩, ⟨527195, 1217, 1216⟩, ⟨528660, 1217, 1216⟩, ⟨530093, 1218, 1216⟩,
  ⟨531591, 1218, 1217⟩, ⟨533083, 1218, 1217⟩, ⟨534590, 1218, 1217⟩, ⟨536056, 1219, 1217⟩,
  ⟨537587, 1219, 1218⟩, ⟨539121, 1219, 1218⟩, ⟨540646, 1219, 1218⟩, ⟨542143, 1220, 1218⟩,
  ⟨543694, 1220, 1219⟩, ⟨545261, 1220, 1219⟩, ⟨546842, 1220, 1219⟩, ⟨548395, 1221, 1219⟩,
  ⟨549982, 1221, 1220⟩, ⟨551582, 1221, 1220⟩, ⟨553195, 1221, 1220⟩, ⟨554780, 1222, 1220⟩,
  ⟨556433, 1222, 1221⟩, ⟨558088, 1222, 1221⟩, ⟨559693, 1223, 1221⟩, ⟨561366, 1223, 1222⟩,
  ⟨563051, 1223, 1222⟩, ⟨564754, 1223, 1222⟩, ⟨566413, 1224, 1222⟩, ⟨568114, 1224, 1223⟩,
  ⟨569833, 1224, 1223⟩, ⟨571570, 1224, 1223⟩, ⟨573279, 1225, 1223⟩, ⟨575043, 1225, 1224⟩,
  ⟨576803, 1225, 1224⟩, ⟨578535, 1226, 1224⟩, ⟨580330, 1226, 1225⟩, ⟨582133, 1226, 1225⟩,
  ⟨583955, 1226, 1225⟩, ⟨585745, 1227, 1225⟩, ⟨587584, 1227, 1226⟩, ⟨589441, 1227, 1226⟩,
  ⟨591259, 1228, 1226⟩, ⟨593139, 1228, 1227⟩, ⟨595036, 1228, 1227⟩, ⟨596938, 1228, 1227⟩,
  ⟨598796, 1229, 1227⟩, ⟨600728, 1229, 1228⟩, ⟨601191, 1229, 1228⟩, ⟨601658, 1229, 1228⟩,
  ⟨602128, 1229, 1228⟩, ⟨602602, 1229, 1228⟩, ⟨603075, 1229, 1228⟩, ⟨603552, 1229, 1228⟩,
  ⟨603985, 1230, 1228⟩, ⟨604476, 1230, 1229⟩, ⟨604971, 1230, 1229⟩, ⟨605467, 1230, 1229⟩,
  ⟨605955, 1230, 1229⟩, ⟨606447, 1230, 1229⟩, ⟨606943, 1230, 1229⟩, ⟨607443, 1230, 1229⟩,
  ⟨607946, 1230, 1229⟩, ⟨608452, 1230, 1229⟩, ⟨608963, 1230, 1229⟩, ⟨609473, 1230, 1229⟩,
  ⟨609987, 1230, 1229⟩, ⟨610457, 1231, 1229⟩, ⟨610987, 1231, 1230⟩, ⟨611521, 1231, 1230⟩,
  ⟨612059, 1231, 1230⟩, ⟨612601, 1231, 1230⟩, ⟨613147, 1231, 1230⟩, ⟨613697, 1231, 1230⟩,
  ⟨614252, 1231, 1230⟩, ⟨614799, 1231, 1230⟩, ⟨615350, 1231, 1230⟩, ⟨615906, 1231, 1230⟩,
  ⟨616461, 1231, 1230⟩, ⟨616972, 1232, 1230⟩, ⟨617543, 1232, 1231⟩, ⟨618118, 1232, 1231⟩,
  ⟨618695, 1232, 1231⟩, ⟨619274, 1232, 1231⟩, ⟨619858, 1232, 1231⟩, ⟨620445, 1232, 1231⟩,
  ⟨621036, 1232, 1231⟩, ⟨621632, 1232, 1231⟩, ⟨622233, 1232, 1231⟩, ⟨622835, 1232, 1231⟩,
  ⟨623429, 1232, 1231⟩, ⟨623978, 1233, 1231⟩, ⟨624589, 1233, 1232⟩, ⟨625205, 1233, 1232⟩,
  ⟨625824, 1233, 1232⟩, ⟨626448, 1233, 1232⟩, ⟨627077, 1233, 1232⟩, ⟨627711, 1233, 1232⟩,
  ⟨628350, 1233, 1232⟩, ⟨628993, 1233, 1232⟩, ⟨629637, 1233, 1232⟩, ⟨630277, 1233, 1232⟩,
  ⟨630939, 1234, 1233⟩, ⟨631605, 1234, 1233⟩, ⟨632277, 1234, 1233⟩, ⟨632940, 1234, 1233⟩,
  ⟨633608, 1234, 1233⟩, ⟨634280, 1234, 1233⟩, ⟨634958, 1234, 1233⟩, ⟨635641, 1234, 1233⟩,
  ⟨636325, 1234, 1233⟩, ⟨637014, 1234, 1233⟩, ⟨637657, 1235, 1233⟩, ⟨638363, 1235, 1234⟩,
  ⟨639076, 1235, 1234⟩, ⟨639794, 1235, 1234⟩, ⟨640517, 1235, 1234⟩, ⟨641245, 1235, 1234⟩,
  ⟨641968, 1235, 1234⟩, ⟨642696, 1235, 1234⟩, ⟨643424, 1235, 1234⟩, ⟨644108, 1236, 1234⟩,
  ⟨644853, 1236, 1235⟩, ⟨645601, 1236, 1235⟩, ⟨646346, 1236, 1235⟩, ⟨647096, 1236, 1235⟩,
  ⟨647851, 1236, 1235⟩, ⟨648612, 1236, 1235⟩, ⟨649380, 1236, 1235⟩, ⟨650153, 1236, 1235⟩,
  ⟨650927, 1236, 1235⟩, ⟨651644, 1237, 1235⟩, ⟨652426, 1237, 1236⟩, ⟨653213, 1237, 1236⟩,
  ⟨654006, 1237, 1236⟩, ⟨654805, 1237, 1236⟩, ⟨655611, 1237, 1236⟩, ⟨656422, 1237, 1236⟩,
  ⟨657240, 1237, 1236⟩, ⟨658060, 1237, 1236⟩, ⟨658834, 1238, 1236⟩, ⟨659671, 1238, 1237⟩,
  ⟨660513, 1238, 1237⟩, ⟨661350, 1238, 1237⟩, ⟨662193, 1238, 1237⟩, ⟨663044, 1238, 1237⟩,
  ⟨663900, 1238, 1237⟩, ⟨664763, 1238, 1237⟩, ⟨665576, 1239, 1237⟩, ⟨666455, 1239, 1238⟩,
  ⟨667340, 1239, 1238⟩, ⟨668233, 1239, 1238⟩, ⟨669132, 1239, 1238⟩, ⟨670039, 1239, 1238⟩,
  ⟨670940, 1239, 1238⟩, ⟨671848, 1239, 1238⟩, ⟨672706, 1240, 1238⟩, ⟨673625, 1240, 1239⟩,
  ⟨674551, 1240, 1239⟩, ⟨675483, 1240, 1239⟩, ⟨676424, 1240, 1239⟩, ⟨677371, 1240, 1239⟩,
  ⟨678324, 1240, 1239⟩, ⟨679286, 1240, 1239⟩, ⟨680201, 1241, 1239⟩, ⟨681166, 1241, 1240⟩,
  ⟨682138, 1241, 1240⟩, ⟨683119, 1241, 1240⟩, ⟨684108, 1241, 1240⟩, ⟨685102, 1241, 1240⟩,
  ⟨686105, 1241, 1240⟩, ⟨687112, 1241, 1240⟩, ⟨688074, 1242, 1240⟩, ⟨689100, 1242, 1241⟩,
  ⟨690134, 1242, 1241⟩, ⟨691163, 1242, 1241⟩, ⟨692200, 1242, 1241⟩, ⟨693245, 1242, 1241⟩,
  ⟨694298, 1242, 1241⟩, ⟨695305, 1243, 1241⟩, ⟨696376, 1243, 1242⟩, ⟨697456, 1243, 1242⟩,
  ⟨698544, 1243, 1242⟩, ⟨699640, 1243, 1242⟩, ⟨700736, 1243, 1242⟩, ⟨701827, 1243, 1242⟩,
  ⟨702873, 1244, 1242⟩, ⟨703988, 1244, 1243⟩, ⟨705108, 1244, 1243⟩, ⟨706236, 1244, 1243⟩,
  ⟨707374, 1244, 1243⟩, ⟨708519, 1244, 1243⟩, ⟨709674, 1244, 1243⟩, ⟨710782, 1245, 1243⟩,
  ⟨711947, 1245, 1244⟩, ⟨713115, 1245, 1244⟩, ⟨714290, 1245, 1244⟩, ⟨715475, 1245, 1244⟩,
  ⟨716668, 1245, 1244⟩, ⟨717815, 1246, 1244⟩, ⟨719035, 1246, 1245⟩, ⟨720263, 1246, 1245⟩,
  ⟨721496, 1246, 1245⟩, ⟨722725, 1246, 1245⟩, ⟨723964, 1246, 1245⟩, ⟨725212, 1246, 1245⟩,
  ⟨726413, 1247, 1245⟩, ⟨727683, 1247, 1246⟩, ⟨728961, 1247, 1246⟩, ⟨730245, 1247, 1246⟩,
  ⟨731539, 1247, 1246⟩, ⟨732843, 1247, 1246⟩, ⟨734085, 1248, 1246⟩, ⟨735403, 1248, 1247⟩,
  ⟨736732, 1248, 1247⟩, ⟨738064, 1248, 1247⟩, ⟨739406, 1248, 1247⟩, ⟨740755, 1248, 1247⟩,
  ⟨742058, 1249, 1247⟩, ⟨743436, 1249, 1248⟩, ⟨744811, 1249, 1248⟩, ⟨746197, 1249, 1248⟩,
  ⟨747587, 1249, 1248⟩, ⟨748988, 1249, 1248⟩, ⟨750342, 1250, 1248⟩, ⟨751774, 1250, 1249⟩,
  ⟨753215, 1250, 1249⟩, ⟨754657, 1250, 1249⟩, ⟨756091, 1250, 1249⟩, ⟨757534, 1250, 1249⟩,
  ⟨758931, 1251, 1249⟩, ⟨760405, 1251, 1250⟩, ⟨761892, 1251, 1250⟩, ⟨763389, 1251, 1250⟩,
  ⟨764891, 1251, 1250⟩, ⟨766346, 1252, 1250⟩, ⟨767861, 1252, 1251⟩, ⟨769389, 1252, 1251⟩,
  ⟨770928, 1252, 1251⟩, ⟨772480, 1252, 1251⟩, ⟨774044, 1252, 1251⟩, ⟨775555, 1253, 1251⟩,
  ⟨777145, 1253, 1252⟩, ⟨778747, 1253, 1252⟩, ⟨780347, 1253, 1252⟩, ⟨781954, 1253, 1252⟩,
  ⟨783506, 1254, 1252⟩, ⟨785139, 1254, 1253⟩, ⟨786785, 1254, 1253⟩, ⟨788445, 1254, 1253⟩,
  ⟨790116, 1254, 1253⟩, ⟨791726, 1255, 1253⟩, ⟨793411, 1255, 1254⟩, ⟨795106, 1255, 1254⟩,
  ⟨796815, 1255, 1254⟩, ⟨798537, 1255, 1254⟩, ⟨800209, 1256, 1254⟩, ⟨801966, 1256, 1255⟩,
  ⟨803715, 1256, 1255⟩, ⟨805478, 1256, 1255⟩, ⟨807254, 1256, 1255⟩, ⟨808974, 1257, 1255⟩,
  ⟨810778, 1257, 1256⟩, ⟨812595, 1257, 1256⟩, ⟨814420, 1257, 1256⟩, ⟨816244, 1257, 1256⟩,
  ⟨818018, 1258, 1256⟩, ⟨819878, 1258, 1257⟩, ⟨821750, 1258, 1257⟩, ⟨823631, 1258, 1257⟩,
  ⟨825526, 1258, 1257⟩, ⟨827373, 1259, 1257⟩, ⟨829291, 1259, 1258⟩, ⟨831223, 1259, 1258⟩,
  ⟨833164, 1259, 1258⟩, ⟨835117, 1259, 1258⟩, ⟨837017, 1260, 1258⟩, ⟨839006, 1260, 1259⟩,
  ⟨840995, 1260, 1259⟩, ⟨842998, 1260, 1259⟩, ⟨844946, 1261, 1259⟩, ⟨846983, 1261, 1260⟩,
  ⟨849032, 1261, 1260⟩, ⟨851098, 1261, 1260⟩, ⟨853181, 1261, 1260⟩, ⟨855193, 1262, 1260⟩,
  ⟨857293, 1262, 1261⟩, ⟨859408, 1262, 1261⟩, ⟨861534, 1262, 1261⟩, ⟨863601, 1263, 1261⟩,
  ⟨865752, 1263, 1262⟩, ⟨867904, 1263, 1262⟩, ⟨870071, 1263, 1262⟩, ⟨872246, 1263, 1262⟩,
  ⟨874458, 1264, 1263⟩, ⟨876678, 1264, 1263⟩, ⟨878916, 1264, 1263⟩, ⟨881155, 1264, 1263⟩,
  ⟨883344, 1265, 1263⟩, ⟨885626, 1265, 1264⟩, ⟨887920, 1265, 1264⟩, ⟨890230, 1265, 1264⟩,
  ⟨892489, 1266, 1264⟩, ⟨894826, 1266, 1265⟩, ⟨897182, 1266, 1265⟩, ⟨899547, 1266, 1265⟩,
  ⟨901864, 1267, 1265⟩, ⟨904277, 1267, 1266⟩, ⟨906706, 1267, 1266⟩, ⟨909137, 1267, 1266⟩,
  ⟨911513, 1268, 1266⟩, ⟨913982, 1268, 1267⟩, ⟨916466, 1268, 1267⟩, ⟨918970, 1268, 1267⟩,
  ⟨921422, 1269, 1267⟩, ⟨923949, 1269, 1268⟩, ⟨926496, 1269, 1268⟩, ⟨929062, 1269, 1268⟩,
  ⟨931579, 1270, 1268⟩, ⟨934195, 1270, 1269⟩, ⟨936823, 1270, 1269⟩, ⟨939456, 1270, 1269⟩,
  ⟨942039, 1271, 1269⟩, ⟨944717, 1271, 1270⟩, ⟨947417, 1271, 1270⟩, ⟨950132, 1271, 1270⟩,
  ⟨952777, 1272, 1270⟩, ⟨955524, 1272, 1271⟩, ⟨958293, 1272, 1271⟩, ⟨961074, 1272, 1271⟩,
  ⟨963806, 1273, 1271⟩, ⟨966641, 1273, 1272⟩, ⟨969477, 1273, 1272⟩, ⟨972254, 1274, 1272⟩,
  ⟨975128, 1274, 1273⟩, ⟨978022, 1274, 1273⟩, ⟨980940, 1274, 1273⟩, ⟨983788, 1275, 1273⟩,
  ⟨986731, 1275, 1274⟩, ⟨989698, 1275, 1274⟩, ⟨992688, 1275, 1274⟩, ⟨995625, 1276, 1274⟩,
  ⟨998666, 1276, 1275⟩, ⟨1001705, 1276, 1275⟩, ⟨1004691, 1277, 1275⟩, ⟨1007785, 1277, 1276⟩,
  ⟨1010904, 1277, 1276⟩, ⟨1014036, 1277, 1276⟩, ⟨1017099, 1278, 1276⟩, ⟨1020272, 1278, 1277⟩,
  ⟨1023467, 1278, 1277⟩, ⟨1026606, 1279, 1277⟩, ⟨1029848, 1279, 1278⟩, ⟨1033094, 1279, 1278⟩,
  ⟨1036365, 1279, 1278⟩, ⟨1039586, 1280, 1278⟩, ⟨1042908, 1280, 1279⟩, ⟨1046255, 1280, 1279⟩,
  ⟨1049532, 1281, 1279⟩, ⟨1052902, 1281, 1280⟩, ⟨1056290, 1281, 1280⟩, ⟨1059705, 1281, 1280⟩,
  ⟨1063065, 1282, 1280⟩, ⟨1066521, 1282, 1281⟩, ⟨1070005, 1282, 1281⟩, ⟨1073425, 1283, 1281⟩,
  ⟨1076961, 1283, 1282⟩, ⟨1080515, 1283, 1282⟩, ⟨1083995, 1284, 1282⟩, ⟨1087582, 1284, 1283⟩,
  ⟨1091198, 1284, 1283⟩, ⟨1094840, 1284, 1283⟩, ⟨1098431, 1285, 1283⟩, ⟨1102111, 1285, 1284⟩,
  ⟨1105815, 1285, 1284⟩, ⟨1109467, 1286, 1284⟩, ⟨1113241, 1286, 1285⟩, ⟨1117010, 1286, 1285⟩,
  ⟨1120728, 1287, 1285⟩, ⟨1124568, 1287, 1286⟩, ⟨1128435, 1287, 1286⟩, ⟨1132242, 1288, 1286⟩,
  ⟨1136146, 1288, 1287⟩, ⟨1140077, 1288, 1287⟩, ⟨1143956, 1289, 1287⟩, ⟨1147951, 1289, 1288⟩,
  ⟨1151974, 1289, 1288⟩, ⟨1155932, 1289, 1288⟩, ⟨1160003, 1290, 1289⟩, ⟨1164095, 1290, 1289⟩,
  ⟨1168221, 1290, 1289⟩, ⟨1172270, 1291, 1289⟩, ⟨1176448, 1291, 1290⟩, ⟨1180650, 1291, 1290⟩,
  ⟨1184795, 1292, 1290⟩, ⟨1189061, 1292, 1291⟩, ⟨1193348, 1292, 1291⟩, ⟨1197568, 1293, 1291⟩,
  ⟨1201920, 1293, 1292⟩, ⟨1204903, 1293, 1292⟩, ⟨1207818, 1294, 1292⟩, ⟨1210848, 1294, 1293⟩,
  ⟨1213885, 1294, 1293⟩, ⟨1216943, 1294, 1293⟩, ⟨1220022, 1294, 1293⟩, ⟨1223029, 1295, 1293⟩,
  ⟨1226158, 1295, 1294⟩, ⟨1229307, 1295, 1294⟩, ⟨1232467, 1295, 1294⟩, ⟨1235555, 1296, 1294⟩,
  ⟨1238765, 1296, 1295⟩, ⟨1241992, 1296, 1295⟩, ⟨1245240, 1296, 1295⟩, ⟨1248416, 1297, 1295⟩,
  ⟨1251705, 1297, 1296⟩, ⟨1255016, 1297, 1296⟩, ⟨1258351, 1297, 1296⟩, ⟨1261613, 1298, 1296⟩,
  ⟨1265000, 1298, 1297⟩, ⟨1268397, 1298, 1297⟩, ⟨1271817, 1298, 1297⟩, ⟨1275164, 1299, 1297⟩,
  ⟨1278637, 1299, 1298⟩, ⟨1282134, 1299, 1298⟩, ⟨1285645, 1299, 1298⟩, ⟨1289081, 1300, 1298⟩,
  ⟨1292643, 1300, 1299⟩, ⟨1296218, 1300, 1299⟩, ⟨1299818, 1300, 1299⟩, ⟨1303345, 1301, 1299⟩,
  ⟨1306991, 1301, 1300⟩, ⟨1310661, 1301, 1300⟩, ⟨1314357, 1301, 1300⟩, ⟨1317979, 1302, 1300⟩,
  ⟨1321728, 1302, 1301⟩, ⟨1325493, 1302, 1301⟩, ⟨1329283, 1302, 1301⟩, ⟨1332999, 1303, 1301⟩,
  ⟨1336847, 1303, 1302⟩, ⟨1340723, 1303, 1302⟩, ⟨1344614, 1303, 1302⟩, ⟨1348425, 1304, 1302⟩,
  ⟨1352370, 1304, 1303⟩, ⟨1356344, 1304, 1303⟩, ⟨1360247, 1305, 1303⟩, ⟨1364268, 1305, 1304⟩,
  ⟨1368317, 1305, 1304⟩, ⟨1372393, 1305, 1304⟩, ⟨1376396, 1306, 1304⟩, ⟨1380533, 1306, 1305⟩,
  ⟨1384687, 1306, 1305⟩, ⟨1388869, 1306, 1305⟩, ⟨1392981, 1307, 1305⟩, ⟨1397228, 1307, 1306⟩,
  ⟨1401503, 1307, 1306⟩, ⟨1405688, 1308, 1306⟩, ⟨1410014, 1308, 1307⟩, ⟨1414365, 1308, 1307⟩,
  ⟨1418745, 1308, 1307⟩, ⟨1423055, 1309, 1307⟩, ⟨1427489, 1309, 1308⟩, ⟨1431952, 1309, 1308⟩,
  ⟨1436343, 1310, 1308⟩, ⟨1440879, 1310, 1309⟩, ⟨1445441, 1310, 1309⟩, ⟨1450023, 1310, 1309⟩,
  ⟨1454532, 1311, 1309⟩, ⟨1459184, 1311, 1310⟩, ⟨1463862, 1311, 1310⟩, ⟨1468455, 1312, 1310⟩,
  ⟨1473197, 1312, 1311⟩, ⟨1477971, 1312, 1311⟩, ⟨1482773, 1312, 1311⟩, ⟨1487499, 1313, 1311⟩,
  ⟨1492364, 1313, 1312⟩, ⟨1497256, 1313, 1312⟩, ⟨1502076, 1314, 1312⟩, ⟨1507048, 1314, 1313⟩,
  ⟨1512045, 1314, 1313⟩, ⟨1516948, 1315, 1313⟩, ⟨1522006, 1315, 1314⟩, ⟨1527098, 1315, 1314⟩,
  ⟨1532113, 1316, 1314⟩, ⟨1537266, 1316, 1315⟩, ⟨1542456, 1316, 1315⟩, ⟨1547681, 1316, 1315⟩,
  ⟨1552829, 1317, 1315⟩, ⟨1558135, 1317, 1316⟩, ⟨1563463, 1317, 1316⟩, ⟨1568714, 1318, 1316⟩,
  ⟨1574118, 1318, 1317⟩, ⟨1579559, 1318, 1317⟩, ⟨1584913, 1319, 1317⟩, ⟨1590422, 1319, 1318⟩,
  ⟨1595967, 1319, 1318⟩, ⟨1601438, 1320, 1318⟩, ⟨1607072, 1320, 1319⟩, ⟨1612726, 1320, 1319⟩,
  ⟨1618297, 1321, 1319⟩, ⟨1624034, 1321, 1320⟩, ⟨1629804, 1321, 1320⟩, ⟨1635486, 1322, 1320⟩,
  ⟨1641334, 1322, 1321⟩, ⟨1647221, 1322, 1321⟩, ⟨1653027, 1323, 1321⟩, ⟨1658988, 1323, 1322⟩,
  ⟨1664990, 1323, 1322⟩, ⟨1670912, 1324, 1322⟩, ⟨1676998, 1324, 1323⟩, ⟨1683128, 1324, 1323⟩,
  ⟨1689161, 1325, 1323⟩, ⟨1695368, 1325, 1324⟩, ⟨1701615, 1325, 1324⟩, ⟨1707788, 1326, 1324⟩,
  ⟨1714114, 1326, 1325⟩, ⟨1720482, 1326, 1325⟩, ⟨1726761, 1327, 1325⟩, ⟨1733211, 1327, 1326⟩,
  ⟨1739692, 1327, 1326⟩, ⟨1746096, 1328, 1326⟩, ⟨1752681, 1328, 1327⟩, ⟨1759304, 1328, 1327⟩,
  ⟨1765836, 1329, 1327⟩, ⟨1772549, 1329, 1328⟩, ⟨1779303, 1329, 1328⟩, ⟨1785977, 1330, 1328⟩,
  ⟨1792820, 1330, 1329⟩, ⟨1799710, 1330, 1329⟩, ⟨1806518, 1331, 1329⟩, ⟨1813510, 1331, 1330⟩,
  ⟨1820536, 1331, 1330⟩, ⟨1827476, 1332, 1330⟩, ⟨1834603, 1332, 1331⟩, ⟨1841652, 1333, 1331⟩,
  ⟨1848866, 1333, 1332⟩, ⟨1856132, 1333, 1332⟩, ⟨1863320, 1334, 1332⟩, ⟨1870702, 1334, 1333⟩,
  ⟨1878110, 1334, 1333⟩, ⟨1885443, 1335, 1333⟩, ⟨1892967, 1335, 1334⟩, ⟨1900537, 1335, 1334⟩,
  ⟨1908012, 1336, 1334⟩, ⟨1915685, 1336, 1335⟩, ⟨1923272, 1337, 1335⟩, ⟨1931059, 1337, 1336⟩,
  ⟨1938880, 1337, 1336⟩, ⟨1946616, 1338, 1336⟩, ⟨1954547, 1338, 1337⟩, ⟨1962531, 1338, 1337⟩,
  ⟨1970420, 1339, 1337⟩, ⟨1978504, 1339, 1338⟩, ⟨1986607, 1339, 1338⟩, ⟨1994817, 1340, 1339⟩,
  ⟨2003057, 1340, 1339⟩, ⟨2011217, 1341, 1339⟩, ⟨2019586, 1341, 1340⟩, ⟨2028012, 1341, 1340⟩,
  ⟨2036334, 1342, 1340⟩, ⟨2044868, 1342, 1341⟩, ⟨2053316, 1343, 1341⟩, ⟨2061969, 1343, 1342⟩,
  ⟨2070663, 1343, 1342⟩, ⟨2079278, 1344, 1342⟩, ⟨2088099, 1344, 1343⟩, ⟨2096983, 1344, 1343⟩,
  ⟨2097151, 1344, 1343⟩
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dyadic_rank_thresholds_valid : RankThresholds dyadicRankThresholds 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma candidate_count_30001 : (candidatePrefix 30001).card ≤ 3265 := by decide +kernel

private lemma prime_count_30001 : (30001:ℕ).primesBelow.card ≤ 3265 :=
  (primes_le_candidates 30000).trans candidate_count_30001

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma dyadic_rank_intervals_valid :
    RankIntervals dyadicRankThresholds 30001 300000 3265 dyadicRankIntervals := by decide +kernel

def countingBound (n : ℕ) : ℕ :=
  if n ≤ 300000 then
    min (countFromIntervals (n+1) 30001 3265 dyadicRankIntervals) (211+48*((n+1)/210+1))
  else 23350+(13*n)/144

lemma counting_bound_small {n : ℕ} (hn : n ≤ 300000) : n.primesLE.card ≤ countingBound n := by
  rw [countingBound, if_pos hn]
  exact le_min (count_from_intervals_valid _ 30001 300000 3265 (n+1) _
      (by decide) (by omega) prime_count_30001 dyadic_rank_intervals_valid) (wheel_prime_count_upper n)

set_option maxRecDepth 100000 in
lemma prime_count_at_65536 : (Nat.primesLE (2^16)).card ≤ 6700 :=
  (counting_bound_small (by decide)).trans (by decide +kernel)

set_option maxRecDepth 100000 in
lemma prime_count_at_262144 : (Nat.primesLE (2^18)).card ≤ 23350 :=
  (counting_bound_small (by decide)).trans (by decide +kernel)

lemma counting_bound_valid (hLinear : ∀ n, 144*n.primesLE.card ≤ 13*n+144*23350)
    (n : ℕ) : n.primesLE.card ≤ countingBound n := by
  by_cases h : n ≤ 300000
  · exact counting_bound_small h
  · rw [countingBound, if_neg h]
    have hL := hLinear n
    omega

def analyticCountingBound (n f : ℕ) : ℕ :=
  (104*(n-1) + 64*(∑ j ∈ range n.log2, countingBound (n/2^(j+1)))) / (f-64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma analytic_rank_intervals_valid :
    NumericRankIntervals dyadicRankThresholds analyticCountingBound 300001 (2^21-1) analyticRankIntervals := by
  decide +kernel

theorem bridge_rank_product (k : ℕ) (hk₁ : 30001 ≤ k) (hk₂ : k ≤ 300000) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) :=
  rank_intervals_bound _ 30001 300000 3265 k _ dyadic_rank_thresholds_valid
    (by decide) hk₁ hk₂ prime_count_30001 dyadic_rank_intervals_valid

theorem analytic_rank_product (k : ℕ) (hk₁ : 300001 ≤ k) (hk₂ : k < 2^21)
    (hEstimate : ∀ n f, 64 < f → 2^f ≤ n^64 → ((range n).filter Nat.Prime).card ≤ analyticCountingBound n f) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) :=
  numeric_rank_intervals_bound _ _ 300001 (2^21-1) k _ dyadic_rank_thresholds_valid
    (by decide) hk₁ (by omega) hEstimate analytic_rank_intervals_valid

end Erdos137OddBridge
