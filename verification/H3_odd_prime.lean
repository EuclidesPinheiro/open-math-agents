import FormalConjectures.ErdosProblems.«137»

/-! Arithmetic lemmas for the odd prime exponent case of Erdős–Selfridge. -/

namespace Erdos137PerfectPower

open Finset

lemma sylvester_schur_lower_bound {k n l p t : ℕ}
    (hl : 2 ≤ l) (hkp : k < p) (ht : t ∈ Ioc n (n + k))
    (hDvd : p ^ l ∣ t) : k ^ l < n := by
  have hInterval := mem_Ioc.mp ht
  have hPos : 0 < t := by omega
  have hUpper : p ^ l ≤ n + k := (Nat.le_of_dvd hPos hDvd).trans hInterval.2
  let r := l - 2
  have hlr : l = r + 2 := by dsimp [r]; omega
  have hRoot : k + 1 ≤ p := by omega
  have hPow : (k + 1) ^ l ≤ p ^ l :=
    (Nat.pow_le_pow_iff_left (by omega : l ≠ 0)).2 hRoot
  have hMono : k ^ r ≤ (k + 1) ^ r := pow_le_pow_left' (by omega) r
  have hGap : k ^ l + (k + 1) ≤ (k + 1) ^ l := by
    by_cases hk : k = 0
    · simp [hk, show l ≠ 0 by omega]
    have hOne : 1 ≤ k ^ r := pow_pos (by omega : 0 < k) r
    rw [hlr, pow_add k, pow_add (k + 1)]
    have hExtra := Nat.mul_le_mul_right (k + 1) hOne
    calc
      k ^ r * k ^ 2 + (k + 1) ≤ k ^ r * (k ^ 2 + (k + 1)) := by
        rw [Nat.mul_add]
        simpa only [Nat.one_mul] using Nat.add_le_add_left hExtra _
      _ ≤ k ^ r * (k + 1) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
      _ ≤ (k + 1) ^ r * (k + 1) ^ 2 := Nat.mul_le_mul_right _ hMono
  have := hGap.trans (hPow.trans hUpper)
  omega

lemma large_prime_factorization_single {k n p t : ℕ}
    (hkp : k ≤ p) (hp : p.Prime) (ht : t ∈ Ioc n (n + k)) (hpt : p ∣ t) :
    (∏ m ∈ Ioc n (n + k), m).factorization p = t.factorization p := by
  have hNonzero : ∀ m ∈ Ioc n (n + k), m ≠ 0 := by
    intro m hm
    have hm' := (mem_Ioc.mp hm).1
    omega
  have htBounds := mem_Ioc.mp ht
  rw [Nat.factorization_prod hNonzero, Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · intro m hm hne
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpm
    have hmBounds := mem_Ioc.mp hm
    rcases lt_or_gt_of_ne hne with h | h
    · have hdiv := Nat.le_of_dvd (show 0 < t - m by omega) (Nat.dvd_sub hpt hpm)
      omega
    · have hdiv := Nat.le_of_dvd (show 0 < m - t by omega) (Nat.dvd_sub hpm hpt)
      omega
  · intro hMissing
    exact (hMissing ht).elim

theorem sylvester_schur_lower_bound_of_no_witness {k n l : ℕ}
    (hl : 2 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ m ∈ Ioc n (n + k), m)
    (hAll : ∀ p : ℕ, k ≤ p → p.Prime →
      l ∣ (∏ m ∈ Ioc n (n + k), m).factorization p) : k ^ l < n := by
  obtain ⟨p, hp, hkp, hProd⟩ := hSylvester
  obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp hProd
  have hmBounds := mem_Ioc.mp hm
  have hmNonzero : m ≠ 0 := by omega
  have hDiv := hAll p hkp.le hp
  rw [large_prime_factorization_single hkp.le hp hm hpm] at hDiv
  have hPos := hp.factorization_pos_of_dvd hmNonzero hpm
  have hPow := (hp.pow_dvd_iff_le_factorization hmNonzero).2 (Nat.le_of_dvd hPos hDiv)
  exact sylvester_schur_lower_bound hl hkp hm hPow

lemma cube_gap {x l : ℕ} (hl : 3 ≤ l) :
    x ^ l + 3 * x ^ (l - 1) ≤ (x + 1) ^ l := by
  let r := l - 3
  have hlr : l = r + 3 := by dsimp [r]; omega
  have hPrev : l - 1 = r + 2 := by omega
  have hMono : x ^ r ≤ (x + 1) ^ r := pow_le_pow_left' (by omega) r
  rw [hPrev, hlr, pow_add x r 3, pow_add x r 2, pow_add (x + 1) r 3]
  calc
    x ^ r * x ^ 3 + 3 * (x ^ r * x ^ 2) =
        x ^ r * (x ^ 3 + 3 * x ^ 2) := by ring
    _ ≤ x ^ r * (x + 1) ^ 3 := Nat.mul_le_mul_left _ (by nlinarith)
    _ ≤ (x + 1) ^ r * (x + 1) ^ 3 := Nat.mul_le_mul_right _ hMono

lemma pair_product_injective {n k i j u v : ℕ}
    (hn : k ^ 2 < n) (hij : i < j) (huv : u < v) (hj : j ≤ k) (hv : v ≤ k)
    (h : (n + i) * (n + j) = (n + u) * (n + v)) : i = u ∧ j = v := by
  have hijBound : i * j ≤ k ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) hj
  have huvBound : u * v ≤ k ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) hv
  have hSums : i + j = u + v := by
    rcases lt_trichotomy (i + j) (u + v) with hlt | heq | hgt
    · have hScale := Nat.mul_le_mul_left n (show i + j + 1 ≤ u + v by omega)
      nlinarith only [hScale, h, hijBound, hn, Nat.zero_le (u * v)]
    · exact heq
    · have hScale := Nat.mul_le_mul_left n (show u + v + 1 ≤ i + j by omega)
      nlinarith only [hScale, h, huvBound, hn, Nat.zero_le (i * j)]
  have hScale := congrArg (fun z : ℕ => n * z) hSums
  have hProds : i * j = u * v := by nlinarith only [hScale, h]
  have hSumsZ : (i : ℤ) + j = (u : ℤ) + v := by exact_mod_cast hSums
  have hProdsZ : (i : ℤ) * j = (u : ℤ) * v := by exact_mod_cast hProds
  have hScaleZ := congrArg (fun z : ℤ => (i : ℤ) * z) hSumsZ
  have hRoots : ((i : ℤ) - u) * ((i : ℤ) - v) = 0 := by
    nlinarith only [hScaleZ, hProdsZ]
  rcases mul_eq_zero.mp hRoots with hLeft | hRight
  · exact ⟨by omega, by omega⟩
  · omega

lemma scaled_pair_gap {n k l a x y : ℕ}
    (hn : k ^ l < n) (hl : 3 ≤ l) (ha : 0 < a)
    (hx : n ^ 2 ≤ a * x ^ l) (hxy : x < y) :
    a * x ^ l + 3 * (n * k) ≤ a * y ^ l := by
  have hnPos : 0 < n := by omega
  have hL : l ≠ 0 := by omega
  let w := a * x ^ (l - 1)
  have hMonoA : a ^ (l - 1) ≤ a ^ l :=
    pow_le_pow_right' (by omega) (Nat.sub_le _ _)
  have hP : (n * k) ^ l < w ^ l := by
    calc
      (n * k) ^ l = n ^ l * k ^ l := mul_pow _ _ _
      _ < n ^ l * n ^ (l - 2) := Nat.mul_lt_mul_of_pos_left
        (hn.trans_le (Nat.le_pow (by omega))) (pow_pos hnPos _)
      _ = (n ^ 2) ^ (l - 1) := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      _ ≤ (a * x ^ l) ^ (l - 1) := pow_le_pow_left' hx _
      _ ≤ w ^ l := by
        dsimp [w]
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm l (l - 1)]
        exact Nat.mul_le_mul_right _ hMonoA
  have hw : n * k ≤ w := ((Nat.pow_lt_pow_iff_left hL).1 hP).le
  have hAtNext := (cube_gap (x := x) hl).trans
    (pow_le_pow_left' (show x + 1 ≤ y by omega) l)
  have hScaled := Nat.mul_le_mul_left a hAtNext
  rw [Nat.mul_add] at hScaled
  have hStep : 3 * (n * k) ≤ a * (3 * x ^ (l - 1)) := by
    calc
      3 * (n * k) ≤ 3 * w := Nat.mul_le_mul_left 3 hw
      _ = a * (3 * x ^ (l - 1)) := by dsimp [w]; ring
  exact (Nat.add_le_add_left hStep _).trans hScaled

theorem distinct_pair_products {n k l : ℕ} {a x : ℕ → ℕ}
    (hk : 0 < k) (hn : k ^ l < n) (hl : 3 ≤ l)
    (ha : ∀ i ≤ k, 0 < a i) (hRepr : ∀ i ≤ k, n + i = a i * x i ^ l)
    {i j u v : ℕ} (hij : i < j) (huv : u < v) (hj : j ≤ k) (hv : v ≤ k)
    (hCoeff : a i * a j = a u * a v) : i = u ∧ j = v := by
  have hL : l ≠ 0 := by omega
  have hnSquare : k ^ 2 < n := (pow_le_pow_right' (by omega : 1 ≤ k)
    (show 2 ≤ l by omega)).trans_lt hn
  have hnk : k < n := (Nat.le_pow (by omega : 0 < l)).trans_lt hn
  let A := a i * a j
  have hA : 0 < A := Nat.mul_pos (ha i (by omega)) (ha j hj)
  let s := x i * x j
  let t := x u * x v
  have hS : (n + i) * (n + j) = A * s ^ l := by
    dsimp [A, s]
    rw [hRepr i (by omega), hRepr j hj, mul_pow]
    ring
  have hT : (n + u) * (n + v) = A * t ^ l := by
    dsimp [A, t]
    rw [hRepr u (by omega), hRepr v hv, ← hCoeff, mul_pow]
    ring
  have hLowS : n ^ 2 ≤ A * s ^ l := by
    rw [← hS, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hLowT : n ^ 2 ≤ A * t ^ l := by
    rw [← hT, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hUpperS : A * s ^ l ≤ (n + k) ^ 2 := by
    rw [← hS, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hUpperT : A * t ^ l ≤ (n + k) ^ 2 := by
    rw [← hT, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hBound : (n + k) ^ 2 < n ^ 2 + 3 * (n * k) := by
    have hMul := Nat.mul_lt_mul_of_pos_right hnk hk
    nlinarith only [hMul]
  have hEqual : s = t := by
    rcases lt_trichotomy s t with hlt | heq | hgt
    · have hGap := scaled_pair_gap hn hl hA hLowS hlt
      omega
    · exact heq
    · have hGap := scaled_pair_gap hn hl hA hLowT hgt
      omega
  apply pair_product_injective hnSquare hij huv hj hv
  rw [hS, hT, hEqual]

lemma factorization_le_of_dvd_difference {p i j : ℕ} (hp : p.Prime)
    (hi : i ≠ 0) (hij : i < j) (hMax : i.factorization p ≤ j.factorization p) :
    i.factorization p ≤ (j - i).factorization p := by
  have hj : j ≠ 0 := by omega
  have hDiff : j - i ≠ 0 := by omega
  let e := i.factorization p
  have hLeft : p ^ e ∣ i := (hp.pow_dvd_iff_le_factorization hi).2 (by rfl)
  have hRight : p ^ e ∣ j := (hp.pow_dvd_iff_le_factorization hj).2 hMax
  exact (hp.pow_dvd_iff_le_factorization hDiff).1 (Nat.dvd_sub hRight hLeft)

-- The deletion lemma is an independent third obligation. The final counting
-- argument also needs the stronger separation of reduced products of
-- multisets of size less than l from Lemma 1 of Erdős–Selfridge.
def restricted_prod_dvd_factorial : Prop :=
  ∀ (n k : ℕ) (a : ℕ → ℕ), 0 < k →
    (∀ t ∈ Ioc n (n + k), a t ∣ t) →
    (∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) →
    ∃ s ⊆ Ioc n (n + k),
      k - ((range k).filter Nat.Prime).card ≤ s.card ∧
      (∏ t ∈ s, a t) ∣ (k - 1).factorial

end Erdos137PerfectPower
