/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Nth

/-!
# The infinite Ramsey theorem

This file proves the infinite Ramsey theorem for finite colourings of the `r`-element subsets of
`ℕ`, for arbitrary arity `r`, and derives the pairs (`RT²`) and triples (`RT³`) cases.

A colouring of `r`-subsets is modelled as a function `c : Finset ℕ → κ` (evaluated only on
finsets of cardinality `r`); a monochromatic set is an infinite `N ⊆ ℕ` such that `c` is
constant on all `r`-subsets of `N`. This is the same interface used by B. Mehta's Lean 3 work
(`inf_ramsey.lean`), which was never ported to Mathlib.

## Main results

* `infinite_ramsey`: for every finite colouring `c` of the `r`-subsets of `ℕ` and every infinite
  `M ⊆ ℕ`, there is an infinite `N ⊆ M` all of whose `r`-subsets get one colour. Proved by
  induction on `r`.
* `infinite_ramsey_seq`: the enumeration form — the monochromatic set can be taken to be the range
  of a strictly monotone `e : ℕ → ℕ`.
* `infinite_ramsey_pairs`, `infinite_ramsey_triples`: the arity `2` and `3` instances.

## Implementation notes

The inductive step is the classical "fan" argument. From an infinite `S`, take the least element
`a = sInf S`; the *link colouring* `e ↦ c (insert a e)` colours the `r`-subsets of `S \ {a}`, so
the induction hypothesis at `r` yields an infinite monochromatic `S' ⊆ S \ {a}` of colour `col`.
Iterating produces a strictly increasing sequence of vertices `a₀ < a₁ < …` with attached
colours `colₙ`; a final pigeonhole on `n ↦ colₙ` selects an infinite subsequence of one colour,
whose `(r+1)`-subsets are all that colour (the least vertex of such a subset plays the role
of `a`).
-/

open Set

set_option autoImplicit false

noncomputable section

/-- Every infinite set of naturals is the range of a strictly monotone `e : ℕ → ℕ`. -/
theorem Set.Infinite.exists_strictMono {s : Set ℕ} (hs : s.Infinite) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, e i ∈ s :=
  ⟨Nat.nth (· ∈ s), Nat.nth_strictMono hs, Nat.nth_mem_of_infinite hs⟩

/-- Pigeonhole over `ℕ`: some colour class of a finite colouring `f : ℕ → κ` is infinite. -/
theorem exists_infinite_fiber_nat {κ : Type*} [Finite κ] (f : ℕ → κ) :
    ∃ k : κ, {n : ℕ | f n = k}.Infinite := by
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber f
  exact ⟨k, Set.infinite_coe_iff.mp hk⟩

variable {κ : Type*}

/-- Intermediate state of the fan construction inside the inductive step of `infinite_ramsey`.
`vert` is a chosen vertex, `succ` an infinite set of naturals all above `vert`, and `hprop`
says: inserting `vert` into any `r`-subset of `succ` gives colour `col` under `c`. -/
private structure RamseyState (c : Finset ℕ → κ) (r : ℕ) where
  vert : ℕ
  col : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt : ∀ x ∈ succ, vert < x
  hprop : ∀ t : Finset ℕ, ↑t ⊆ succ → t.card = r → c (insert vert t) = col

/-- **The infinite Ramsey theorem** (general arity, relativized). For every finite colouring
`c` of the `r`-element finite subsets of `ℕ` and every infinite `M ⊆ ℕ`, there is an infinite
`N ⊆ M` all of whose `r`-subsets receive one colour.

Proof by induction on `r`; see the module docstring for the fan argument driving the step. -/
theorem infinite_ramsey [Finite κ] (r : ℕ) (c : Finset ℕ → κ)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N ⊆ M, N.Infinite ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c t = col := by
  induction r generalizing c M with
  | zero =>
    -- The only `0`-subset is `∅`, so `M` itself is monochromatic of colour `c ∅`.
    refine ⟨M, subset_rfl, hM, c ∅, fun t _ ht => ?_⟩
    rw [Finset.card_eq_zero.mp ht]
  | succ r ih =>
    -- One fan step: from an infinite `S`, pick `a' = sInf S` and, by the IH applied to the link
    -- colouring `e ↦ c (insert a' e)` on `S \ {a'}`, an infinite monochromatic `N ⊆ S`.
    have stepCore : ∀ S : Set ℕ, S.Infinite →
        ∃ a' ∈ S, ∃ (col' : κ) (N : Set ℕ),
          N.Infinite ∧ N ⊆ S ∧ (∀ x ∈ N, a' < x) ∧
          ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c (insert a' t) = col' := by
      intro S hS
      refine ⟨sInf S, Nat.sInf_mem hS.nonempty, ?_⟩
      have hle : ∀ x ∈ S, sInf S ≤ x := fun x hx => Nat.sInf_le hx
      have hdiff : (S \ {sInf S}).Infinite := hS.diff (Set.finite_singleton _)
      obtain ⟨N, hNsub, hNinf, col', hmono⟩ := ih (fun e => c (insert (sInf S) e)) hdiff
      refine ⟨col', N, hNinf, hNsub.trans Set.diff_subset, ?_, hmono⟩
      intro x hxN
      have hxd := hNsub hxN
      exact lt_of_le_of_ne (hle x hxd.1) fun h => hxd.2 (h ▸ rfl)
    -- Package a step as a state transition.
    have advance : ∀ s : RamseyState c r, ∃ s' : RamseyState c r,
        s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
      intro s
      obtain ⟨a', ha'mem, col', N, hNinf, hNsub, hNgt, hNprop⟩ := stepCore s.succ s.hInf
      exact ⟨⟨a', col', N, hNinf, hNgt, hNprop⟩, ha'mem, hNsub⟩
    -- Initial state from `M`, then the fan sequence of states.
    obtain ⟨a₀, ha₀M, col₀, N₀, hN₀inf, hN₀sub, hN₀gt, hN₀prop⟩ := stepCore M hM
    let s₀ : RamseyState c r := ⟨a₀, col₀, N₀, hN₀inf, hN₀gt, hN₀prop⟩
    let states : ℕ → RamseyState c r := fun n => n.rec s₀ fun _ s => (advance s).choose
    have I1 : ∀ n, (states (n + 1)).vert ∈ (states n).succ :=
      fun n => (advance (states n)).choose_spec.1
    have I2 : ∀ n, (states (n + 1)).succ ⊆ (states n).succ :=
      fun n => (advance (states n)).choose_spec.2
    have I3 : ∀ n, (states n).vert < (states (n + 1)).vert :=
      fun n => (states n).hgt _ (I1 n)
    have I4 : ∀ m n, m ≤ n → (states n).succ ⊆ (states m).succ := by
      intro m n hmn
      induction n with
      | zero => simp [Nat.le_zero.mp hmn]
      | succ n ih2 =>
        rcases Nat.lt_or_eq_of_le hmn with h | rfl
        · exact (I2 n).trans (ih2 (Nat.lt_succ_iff.mp h))
        · exact subset_rfl
    have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
      intro m n hmn
      cases n with
      | zero => exact absurd hmn (Nat.not_lt_zero m)
      | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
    have vmono : StrictMono fun n => (states n).vert := strictMono_nat_of_lt_succ I3
    -- Every vertex lies in `M`.
    have hsuccM : ∀ n, (states n).succ ⊆ M := fun n => (I4 0 n (Nat.zero_le n)).trans hN₀sub
    have hvertM : ∀ n, (states n).vert ∈ M := by
      intro n
      cases n with
      | zero => exact ha₀M
      | succ n => exact hsuccM n (I1 n)
    -- Final pigeonhole on the fan colours.
    obtain ⟨col, hJinf⟩ := exists_infinite_fiber_nat (fun n => (states n).col)
    set V : ℕ → ℕ := fun n => (states n).vert with hV
    set J : Set ℕ := {n | (states n).col = col} with hJ
    refine ⟨V '' J, ?_, hJinf.image (vmono.injective.injOn), col, ?_⟩
    · rintro x ⟨n, _, rfl⟩; exact hvertM n
    · intro t htN htcard
      -- The least vertex `a` of `t` is `vertₘ` for some `m` with `colₘ = col`; the remaining
      -- `r` vertices have index `> m`, hence lie in `(states m).succ`, so `hprop` applies.
      have ht_ne : t.Nonempty := Finset.card_pos.mp (by rw [htcard]; exact Nat.succ_pos r)
      set a := t.min' ht_ne with ha
      have ha_mem : a ∈ t := Finset.min'_mem _ _
      obtain ⟨m, hmJ, hVm⟩ : ∃ m, (states m).col = col ∧ (states m).vert = a := by
        obtain ⟨m, hmJ, hVm⟩ := htN (Finset.mem_coe.mpr ha_mem)
        exact ⟨m, hmJ, hVm⟩
      have hsub : ↑(t.erase a) ⊆ (states m).succ := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_erase] at hx
        obtain ⟨hxne, hxt⟩ := hx
        obtain ⟨p, hpJ, hVp⟩ := htN (Finset.mem_coe.mpr hxt)
        have hax : a < x := lt_of_le_of_ne (Finset.min'_le t x hxt) (Ne.symm hxne)
        have hmp : m < p := by
          have h1 : (states m).vert < (states p).vert := by
            rw [hVm, show (states p).vert = x from hVp]; exact hax
          exact vmono.lt_iff_lt.mp h1
        have := I5 m p hmp
        rwa [show (states p).vert = x from hVp] at this
      have hcard : (t.erase a).card = r := by
        rw [Finset.card_erase_of_mem ha_mem, htcard]; omega
      have key := (states m).hprop (t.erase a) hsub hcard
      rw [hVm, Finset.insert_erase ha_mem, hmJ] at key
      exact key

/-- **Enumeration form of the infinite Ramsey theorem.** The monochromatic set may be taken to be
the range of a strictly monotone `e : ℕ → ℕ`. -/
theorem infinite_ramsey_seq [Finite κ] (r : ℕ) (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = r → c t = col := by
  obtain ⟨N, _, hNinf, col, hcol⟩ := infinite_ramsey r c (M := Set.univ) Set.infinite_univ
  obtain ⟨e, he, hmem⟩ := hNinf.exists_strictMono
  exact ⟨e, he, col, fun t htsub htcard =>
    hcol t (htsub.trans (Set.range_subset_iff.mpr hmem)) htcard⟩

/-- **The infinite Ramsey theorem for pairs (RT²)**, as the arity-`2` instance. -/
theorem infinite_ramsey_pairs [Finite κ] (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = 2 → c t = col :=
  infinite_ramsey_seq 2 c

/-- **The infinite Ramsey theorem for triples (RT³)**, as the arity-`3` instance. -/
theorem infinite_ramsey_triples [Finite κ] (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = 3 → c t = col :=
  infinite_ramsey_seq 3 c

end

/-!
## Verification

The two `#guard_msgs` blocks below make the build **fail** if the headline theorems ever depend
on anything beyond the three standard axioms of classical mathematics — in particular if a
`sorry` (which would surface as `sorryAx`) ever slips in. They are the self-contained analogue of
an axiom audit, and CI runs them on every push.
-/

/-- info: 'infinite_ramsey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinite_ramsey

/-- info: 'infinite_ramsey_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinite_ramsey_seq
