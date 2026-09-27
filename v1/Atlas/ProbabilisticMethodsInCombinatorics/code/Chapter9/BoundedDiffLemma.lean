/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option maxHeartbeats 400000

namespace BoundedDiffLemma

/-- A single term in the union-bound used in Lemma 9.3.5: the expected number of vertex
subsets of size $t$ in $G(n, p)$ that contain at least $\lceil 3t/2 \rceil$ edges, bounded
by $\binom{n}{t}\binom{t(t-1)/2}{3t/2} p^{3t/2}$. -/
noncomputable def unionBoundTerm (n t : ℕ) (p : ℝ) : ℝ :=
  (↑(Nat.choose n t) : ℝ) *
  (↑(Nat.choose (t * (t - 1) / 2) (3 * t / 2)) : ℝ) *
  p ^ (3 * t / 2)

/-- Sum of the union-bound terms over subset sizes $t = 4, 5, \dots, k+3$. -/
noncomputable def unionBoundSum (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.range k, unionBoundTerm n (t + 4) p

/-- The number of subset sizes $t$ to sum over in the union bound: $\lfloor C\sqrt{n} \rfloor - 3$. -/
noncomputable def numTerms (C : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (C * Real.sqrt (n : ℝ)) - 3

open Classical in
/-- The probability that the random graph $G(n,p)$ contains a non-3-colorable subset of
size at most $C\sqrt{n}$: the $G(n,p)$-weight of all graphs on `Fin n`
having a vertex set `S` with `|S| ≤ C√n` whose induced subgraph is not
3-colorable. -/
noncomputable def gnpNon3ColorableSmallSubsetProb (n : ℕ) (p : ℝ) (C : ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n),
    if ∃ S : Finset (Fin n), (S.card : ℝ) ≤ C * Real.sqrt n ∧
        ¬ (G.induce (S : Set (Fin n))).Colorable 3
    then p ^ G.edgeFinset.card * (1 - p) ^ (n.choose 2 - G.edgeFinset.card)
    else 0

/-- The union-bound upper estimate: the probability of having a non-3-colorable subset of
size $\leq C\sqrt{n}$ is bounded by the union-bound sum. -/
theorem unionBound_upper_bound (n : ℕ) (p : ℝ) (C : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    gnpNon3ColorableSmallSubsetProb n p C ≤ unionBoundSum n p (numTerms C n) := by sorry

/-- For $\alpha > 5/6$ and $p \leq n^{-\alpha}$, the union-bound sum vanishes as $n \to \infty$:
for any $\varepsilon > 0$ there exists $N$ such that for all $n \geq N$ the sum is $< \varepsilon$. -/
theorem unionBoundSum_lt_of_large
    (α : ℝ) (hα : α > 5 / 6) (C : ℝ) (hC : 0 < C) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ p : ℝ, 0 ≤ p → p ≤ Real.rpow (n : ℝ) (-α) →
        unionBoundSum n p (numTerms C n) < ε := by sorry

/-- Lemma 9.3.5: for $\alpha > 5/6$, $p \leq n^{-\alpha}$, and large enough $n$, every subset
of $\leq C\sqrt{n}$ vertices in $G(n,p)$ is 3-colorable with high probability. -/
theorem small_subset_three_colorable
    (α : ℝ) (hα : α > 5 / 6) (C : ℝ) (hC : 0 < C) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ p : ℝ, 0 ≤ p → p ≤ Real.rpow (n : ℝ) (-α) →
        gnpNon3ColorableSmallSubsetProb n p C < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := unionBoundSum_lt_of_large α hα C hC ε hε
  refine ⟨max N 1, fun n hn p hp hpn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast le_trans (le_max_right N 1) hn
  have hp1 : p ≤ 1 :=
    hpn.trans (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
  exact lt_of_le_of_lt (unionBound_upper_bound n p C hp hp1)
    (hN n (le_trans (le_max_left N 1) hn) p hp hpn)

end BoundedDiffLemma
