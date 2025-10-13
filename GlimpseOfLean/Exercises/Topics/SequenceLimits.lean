import GlimpseOfLean.Library.Basic

namespace Topics

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.

There are many exercises in this file, so do not hesitate to take a
look at the solutions folder if you are stuck, there will be other
exercises.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  linarith

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  linarith

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:
-/

/-- Definition of “u tends to l” -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|l - l|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by
  intro ε hh
  use 0
  intro n hn
  specialize h n
  rw [h]
  simp
  linarith



/-
A small user interface remark: you may have noticed in the previous example that
your editor shows a somewhat ghostly `{u l}` after the `example` word.
This text is not actually present in the Lean file, and cannot be edited.
It is displayed as a hint that Lean inferred we wanted to work with some `u` and `l`.
The fact that `u` should be a sequence and `l` a real numbered was inferred because
the announced conclusion was `seq_limit u l`.

The short version of the above paragraph is you can mostly ignore those ghostly
indications and trust your common sense that `u` is a sequence and `l` a limit.
-/

/-
When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by
  specialize h (l/2) (by linarith)
  rcases h with ⟨n, hh⟩
  use n
  intro n₁ h'
  specialize hh n₁
  apply hh at h'
  apply abs_le.mp at h'
  linarith







/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith


/- Let's do something similar: the squeezing theorem.
In that example it can help to use the `specialize` tactic (introduced in the file
`03Forall.lean`) so that the `linarith` tactic can pick up the relevant files
from the assumptions.
-/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by
  intro e e_pos
  specialize hu e e_pos
  specialize hw e e_pos
  rcases hu with ⟨a, ha⟩
  rcases hw with ⟨b, hb⟩
  use (max a b)
  intro n hn
  specialize ha n (by exact le_of_max_le_left hn)
  specialize hb n (by exact le_of_max_le_right hn)
  specialize h n
  specialize h' n
  rw [abs_le] at *
  constructor
  . linarith
  . linarith



/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma unique_limit : seq_limit u l → seq_limit u l' → l = l' := by
  intro h h'
  apply eq_of_abs_sub_le_all
  intro e e_pos
  specialize h (e/2) (by linarith)
  specialize h' (e/2) (by linarith)
  rcases h with ⟨n, hn⟩
  rcases h' with ⟨n', hn'⟩
  specialize hn (max n n') (by simp)
  specialize hn' (max n n') (by simp)
  have h : |u (max n n') - l| + |u (max n n') - l'| ≤ e/2 + e/2 := by exact add_le_add hn hn'
  rw [abs_sub_comm, abs_sub_comm (u _)] at h
  have : e/2 + e/2 = e := by simp
  rw [← this]
  apply le_trans _ h
  apply abs_sub_le'



/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by
  intro e e_pos
  rcases h with ⟨h_sup, h_reach_sup⟩
  specialize h_reach_sup e e_pos
  rcases h_reach_sup with ⟨n₁, h⟩
  use n₁
  intro n₂ hge
  specialize h' n₁ n₂ (by linarith)
  have :u n₂ ≥ M -e := by linarith
  specialize h_sup n₂
  rw [abs_le]
  constructor
  . linarith
  . linarith



/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.
-/

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

/-
In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])


/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  intro hyp n n'
  use max (φ n) (φ n')
  constructor
  have := (id_le_extraction' hyp)
  specialize this n'
  simp
  . exact Or.inr this
  . have := id_le_extraction' hyp
    specialize this (max (φ n) (φ n'))
    apply ge_trans this
    simp
    apply Or.inl
    apply id_le_extraction'
    exact hyp







/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.
-/

def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
  intro hyp e e_pos n
  rcases hyp with ⟨φ, ⟨ex, sl⟩⟩
  specialize sl e e_pos
  rcases sl with ⟨n', h⟩
  use φ (max n n')
  specialize h (max n n') (by exact Nat.le_max_right n n')
  constructor
  . calc
      φ (max n n') ≥ max n n' := by apply id_le_extraction'; exact ex
      _            ≥ n := by exact Nat.le_max_left n n'
  . exact h












/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by
  intro e e_pos
  specialize h e e_pos
  have := extraction_ge hφ
  rcases h with ⟨n₁, h⟩
  use n₁
  intro n₂ hp
  specialize h (φ n₂) (
    by calc
      φ n₂ ≥ n₂ := by apply id_le_extraction'; simpa
    _ ≥ n₁ := by simpa
    )
  have h':= hφ n₁ n₂
  exact h






/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by
  have h' := near_cluster ha
  apply eq_of_abs_sub_le_all
  intro e e_pos
  specialize hl (e/2) (by linarith)
  rcases hl with ⟨n, hn⟩
  specialize h' (e/2) (by linarith) n
  rcases h' with ⟨n₂, ⟨hge, hle⟩⟩
  specialize hn n₂ (by linarith)
  have h : |u n₂ - l| + |a - u n₂| ≤ e := by
    rw [abs_sub_comm a _]
    linarith
  trans |u n₂ -l| + |a-u n₂|
  . have : a-l = (u n₂ -l) + (a - u n₂) := by linarith
    rw [this]
    apply abs_add_le
  . exact h


/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by
  intro h
  rcases h with ⟨l, hl⟩
  intro e e_pos
  specialize hl (e/2) (by linarith)
  rcases hl with ⟨n, hn⟩
  use n
  intro p q hp hq
  have pp := hn p hp
  have qq := hn q hq
  have := add_le_add pp qq
  simp at *
  rw [abs_sub_comm (u q) _] at this
  trans |u p - l| + |l - u q|
  . exact abs_sub_le (u p) l (u q)
  . exact this








/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  have := near_cluster hl
  intro e e_pos
  specialize hu (e/2) (by linarith)
  rcases hu with ⟨n₁, h1⟩
  specialize this (e/2) (by linarith) n₁
  rcases this with ⟨n₂, ⟨hge, h2⟩⟩
  use n₁
  intro n₃ h3
  have := h1 _ _ hge h3
  have := add_le_add h2 this
  conv at this =>
    congr
    . rw [add_comm]
      rw [abs_sub_comm]
  simp at this
  trans |u n₃ - u n₂| + |u n₂ - l|
  . apply abs_sub_le
  . assumption
