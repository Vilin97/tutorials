import tuto_lib
/-
This file continues the elementary study of limits of sequences. 
It can be skipped if the previous file was too easy, it won't introduce
any new tactic or trick.

Remember useful lemmas:

abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub_comm (x y : ℝ) : |x - y| = |y - x|

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

and the definition:

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

You can also use a property proved in the previous file:

unique_limit : seq_limit u l → seq_limit u l' → l = l'

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m
-/


variable { φ : ℕ → ℕ}

/-
The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete 
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
  { exact nat.zero_le _ },
  { exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]) },
end

/-- Extractions take arbitrarily large values for arbitrarily large 
inputs. -/
-- 0039
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros h M N,
  let n := M + N,
  use n,
  split,
  linarith,
  calc M ≤ n : by linarith
    ...  ≤ φ n : id_le_extraction' h n,
end

/-- A real number `a` is a cluster point of a sequence `u` 
if `u` has a subsequence converging to `a`. 

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a
-/

variables {u : ℕ → ℝ} {a l : ℝ}

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
Lean can read this abbreviation, but displays it as the confusing:
`∃ (n : ℕ) (H : n ≥ N)`
One gets used to it. Alternatively, one can get rid of it using the lemma
  exists_prop {p q : Prop} : (∃ (h : p), q) ↔ p ∧ q
-/

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
-- 0040
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros h ε ε_pos M,
  rcases h with ⟨φ, φ_ext, hl ⟩,
  cases (hl ε ε_pos) with N hN,
  rcases (extraction_ge φ_ext M N) with ⟨ n, hn, h_φn⟩,
  exact ⟨φ n, h_φn, hN n hn⟩,
end

/-
The above exercice can be done in five lines. 
Hint: you can use the anonymous constructor syntax when proving
existential statements.
-/

/-- If `u` tends to `l` then its subsequences tend to `l`. -/
-- 0041
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l :=
begin
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N,
  intros n hn,
  exact hN (φ n) (by linarith [id_le_extraction' hφ n]),
end

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
-- 0042
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l :=
begin
  rcases ha with ⟨ φ, φ_ext, h⟩,
  apply unique_limit h,
  exact subseq_tendsto_of_tendsto' hl φ_ext,
end

/-- Cauchy_sequence sequence -/
def cauchy_sequence (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- 0043
example : (∃ l, seq_limit u l) → cauchy_sequence u :=
begin
  rintros ⟨l, hl⟩ ε ε_pos,
  cases hl (ε/2) (by linarith) with N hN,
  use N,
  intros p q hp hq,
  calc |u p - u q| = |(u p - l) + (l - u q)| : by ring_nf
               ... ≤ |(u p - l)| + |(l - u q)| : abs_add (u p - l) (l - u q)
               ... = |u p - l| + |u q - l| : by rw abs_sub_comm l (u q)
               ... ≤ ε : by linarith [hN p hp, hN q hq],
end


/- 
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/
-- 0044
example (hu : cauchy_sequence u) (hl : cluster_point u l) : seq_limit u l :=
begin
  intros ε ε_pos,
  cases hu (ε/2) (by linarith) with N hN,
  rcases hl with ⟨ φ, φ_ext, φ_hl ⟩,
  cases φ_hl (ε/2) (by linarith) with N' hN',
  use N + N',
  intros n hn,
  have key1 : φ n ≥ N,
    linarith [id_le_extraction φ_ext n],
  have key2 : |(u n - (u ∘ φ) n)| ≤ ε/2,
    exact hN n (φ n) (by linarith) key1,
  calc |u n - l| = |(u n - (u ∘ φ) n) + ((u ∘ φ) n - l)| : by ring_nf
             ... ≤ |(u n - (u ∘ φ) n)| + |((u ∘ φ) n - l)| : abs_add (u n - (u ∘ φ) n) ((u ∘ φ) n - l)
             ... ≤ ε : by linarith [hN' n (by linarith)],
end

