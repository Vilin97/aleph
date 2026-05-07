import Mathlib
import Submission.Helpers

open SimpleGraph

namespace Submission

def ramseyFinsetBound (r s n : ℕ) : Prop :=
  ∀ {α : Type} (G : SimpleGraph α) (t : Finset α),
    G.CliqueFreeOn (t : Set α) r →
    Gᶜ.CliqueFreeOn (t : Set α) s →
    t.card < n

def ramseyFinsetBound_apply {r s n : ℕ} {α : Type*}
    (h : ∀ (G : SimpleGraph α) (t : Finset α),
      G.CliqueFreeOn (t : Set α) r →
      Gᶜ.CliqueFreeOn (t : Set α) s →
      t.card < n)
    (G : SimpleGraph α) (t : Finset α)
    (hG : G.CliqueFreeOn (t : Set α) r)
    (hGc : Gᶜ.CliqueFreeOn (t : Set α) s) : t.card < n :=
  h G t hG hGc

theorem ramsey_finset_base_left: ∀ {s : ℕ}, 2 ≤ s → ramseyFinsetBound 2 s s := by
  intro s hs α G t h2 hs'
  classical
  by_contra hlt
  have hst : s ≤ t.card := Nat.not_lt.mp hlt
  obtain ⟨u, hut, hus⟩ := Finset.exists_subset_card_eq hst
  have hpair_t : (t : Set α).Pairwise (G.Adjᶜ) :=
    (SimpleGraph.cliqueFreeOn_two (G := G) (s := (t : Set α))).1 h2
  have hclique_u : Gᶜ.IsClique (u : Set α) := by
    rw [SimpleGraph.isClique_iff]
    intro a ha b hb hab
    exact (SimpleGraph.compl_adj G a b).2 ⟨hab, by simpa using hpair_t (hut ha) (hut hb) hab⟩
  exact hs' (show (u : Set α) ⊆ (t : Set α) from by
    intro x hx
    exact hut hx) ⟨hclique_u, hus⟩

theorem ramsey_finset_base_right: ∀ {r : ℕ}, 2 ≤ r → ramseyFinsetBound r 2 r := by
  intro r hr
  unfold ramseyFinsetBound
  intro α G t hGr hGc2
  have hGr' : Gᶜᶜ.CliqueFreeOn (t : Set α) r := by
    simpa [compl_compl] using hGr
  exact ramsey_finset_base_left (s := r) hr (G := Gᶜ) (t := t) hGc2 hGr'

theorem ramsey_neighbor_partition_card: ∀ {α : Type*} [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (t : Finset α) (a : α),
    (t.erase a).card =
      ((t.erase a).filter fun x => x ∈ G.neighborSet a).card +
      ((t.erase a).filter fun x => x ∈ Gᶜ.neighborSet a).card := by
  classical
  intro α _ G _ t a
  let s := t.erase a
  have hs_union :
      (s.filter fun x => x ∈ G.neighborSet a) ∪ (s.filter fun x => x ∈ Gᶜ.neighborSet a) = s := by
    ext x
    by_cases hxa : x = a
    · simp [s, hxa]
    · have hxa' : a ≠ x := by simpa [eq_comm] using hxa
      by_cases hax : G.Adj a x
      · simp [s, hxa, hxa', hax, SimpleGraph.compl_adj]
      · simp [s, hxa, hxa', hax, SimpleGraph.compl_adj]
  have hs_disj :
      Disjoint (s.filter fun x => x ∈ G.neighborSet a) (s.filter fun x => x ∈ Gᶜ.neighborSet a) := by
    refine Finset.disjoint_filter.2 ?_
    intro x hx hxadj hxcomp
    have h1 : G.Adj a x := by
      simpa using hxadj
    have h2 : a ≠ x ∧ ¬ G.Adj a x := by
      simpa [SimpleGraph.compl_adj] using hxcomp
    exact h2.2 h1
  calc
    s.card = ((s.filter fun x => x ∈ G.neighborSet a) ∪ (s.filter fun x => x ∈ Gᶜ.neighborSet a)).card := by
      rw [hs_union]
    _ = (s.filter fun x => x ∈ G.neighborSet a).card + (s.filter fun x => x ∈ Gᶜ.neighborSet a).card := by
      exact (Finset.card_union_eq_card_add_card).2 hs_disj


theorem ramsey_finset_step: ∀ {r s n₁ n₂ : ℕ}, 2 ≤ r → 2 ≤ s →
    ramseyFinsetBound (r - 1) s n₁ →
    ramseyFinsetBound r (s - 1) n₂ →
    ramseyFinsetBound r s (n₁ + n₂ + 1) := by
  intro r s n₁ n₂ hr hs hrec1 hrec2
  classical
  intro α G t hG hGc
  by_contra hcard
  have hge : n₁ + n₂ + 1 ≤ t.card := Nat.not_lt.mp hcard
  have ht_pos : 0 < t.card := by
    have hpos : 0 < n₁ + n₂ + 1 := by omega
    omega
  rcases Finset.card_pos.mp ht_pos with ⟨a, ha⟩
  let u := (t.erase a).filter fun x => x ∈ G.neighborSet a
  let v := (t.erase a).filter fun x => x ∈ Gᶜ.neighborSet a
  have hpart : (t.erase a).card = u.card + v.card := by
    simpa only [u, v] using ramsey_neighbor_partition_card (G := G) t a
  have herase : (t.erase a).card + 1 = t.card := Finset.card_erase_add_one ha
  have hcard' : t.card = u.card + v.card + 1 := by
    rw [← herase, hpart]
  have hu_subset_t : (u : Set α) ⊆ t := by
    intro x hx
    change x ∈ u at hx
    simp only [u, Finset.mem_filter, Finset.mem_erase] at hx
    exact hx.1.2
  have hv_subset_t : (v : Set α) ⊆ t := by
    intro x hx
    change x ∈ v at hx
    simp only [v, Finset.mem_filter, Finset.mem_erase] at hx
    exact hx.1.2
  have hu_subset_inter : (u : Set α) ⊆ (t : Set α) ∩ G.neighborSet a := by
    intro x hx
    change x ∈ u at hx
    simp only [u, Finset.mem_filter, Finset.mem_erase] at hx
    exact ⟨hx.1.2, hx.2⟩
  have hv_subset_inter : (v : Set α) ⊆ (t : Set α) ∩ Gᶜ.neighborSet a := by
    intro x hx
    change x ∈ v at hx
    simp only [v, Finset.mem_filter, Finset.mem_erase] at hx
    exact ⟨hx.1.2, hx.2⟩
  have ha_set : a ∈ (t : Set α) := ha
  have hG' := hG
  rw [show r = (r - 1) + 1 by omega] at hG'
  have hGc' := hGc
  rw [show s = (s - 1) + 1 by omega] at hGc'
  have hG_inter : G.CliqueFreeOn ((t : Set α) ∩ G.neighborSet a) (r - 1) :=
    SimpleGraph.CliqueFreeOn.of_succ (G := G) hG' ha_set
  have hGc_inter : Gᶜ.CliqueFreeOn ((t : Set α) ∩ Gᶜ.neighborSet a) (s - 1) :=
    SimpleGraph.CliqueFreeOn.of_succ (G := Gᶜ) hGc' ha_set
  have hG_u : G.CliqueFreeOn (u : Set α) (r - 1) :=
    SimpleGraph.CliqueFreeOn.subset (G := G) hu_subset_inter hG_inter
  have hGc_u : Gᶜ.CliqueFreeOn (u : Set α) s :=
    SimpleGraph.CliqueFreeOn.subset (G := Gᶜ) hu_subset_t hGc
  have hu_lt : u.card < n₁ := by
    exact hrec1 G u hG_u hGc_u
  have hG_v : G.CliqueFreeOn (v : Set α) r :=
    SimpleGraph.CliqueFreeOn.subset (G := G) hv_subset_t hG
  have hGc_v : Gᶜ.CliqueFreeOn (v : Set α) (s - 1) :=
    SimpleGraph.CliqueFreeOn.subset (G := Gᶜ) hv_subset_inter hGc_inter
  have hv_lt : v.card < n₂ := by
    exact hrec2 G v hG_v hGc_v
  have ht_lt : t.card < n₁ + n₂ + 1 := by
    rw [hcard']
    omega
  exact hcard ht_lt

theorem ramsey_finset_bound: ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ramseyFinsetBound r s n := by
  intro r s hr hs
  let P : ℕ → Prop := fun m =>
    ∀ r s : ℕ, r + s = m → 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ramseyFinsetBound r s n
  have hP : ∀ m : ℕ, P m := by
    intro m
    induction' m using Nat.strong_induction_on with m ih
    intro r s hsum hr hs
    by_cases hr2 : r = 2
    · subst hr2
      refine ⟨s, ?_⟩
      exact ramsey_finset_base_left hs
    · by_cases hs2 : s = 2
      · subst hs2
        refine ⟨r, ?_⟩
        exact ramsey_finset_base_right hr
      · have hr3 : 3 ≤ r := by omega
        have hs3 : 3 ≤ s := by omega
        have h1 : (r - 1) + s < m := by omega
        have h2 : r + (s - 1) < m := by omega
        rcases ih ((r - 1) + s) h1 (r - 1) s rfl (by omega) hs with ⟨n1, hn1⟩
        rcases ih (r + (s - 1)) h2 r (s - 1) rfl hr (by omega) with ⟨n2, hn2⟩
        refine ⟨n1 + n2 + 1, ?_⟩
        exact ramsey_finset_step hr hs hn1 hn2
  exact hP (r + s) r s rfl hr hs

theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  intro r s hr hs
  rcases ramsey_finset_bound r s hr hs with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro G
  by_contra h
  push_neg at h
  rcases h with ⟨hG, hGc⟩
  have h1 : G.CliqueFreeOn ((Finset.univ : Finset (Fin n)) : Set (Fin n)) r := by
    exact hG.cliqueFreeOn (s := ((Finset.univ : Finset (Fin n)) : Set (Fin n)))
  have h2 : Gᶜ.CliqueFreeOn ((Finset.univ : Finset (Fin n)) : Set (Fin n)) s := by
    exact hGc.cliqueFreeOn (s := ((Finset.univ : Finset (Fin n)) : Set (Fin n)))
  have hlt : (Finset.univ : Finset (Fin n)).card < n := hn G Finset.univ h1 h2
  simpa using hlt


end Submission
