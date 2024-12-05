import Mathlib.Tactic


lemma lema1 (P: Prop) : P → P := by
  intro hP
  exact hP

axiom  my_falso: Prop
axiom  my_falso_def:(∀ P: Prop, my_falso → P)

lemma lema2 : False ↔  my_falso := by
  constructor
  intro h
  exfalso
  exact h
  apply my_falso_def

def my_no (P: Prop) := P → my_falso

axiom  PL3 (P: Prop) : (my_no P → P ) →  P


lemma lema3 {X:Type} (A B C: Set X): A ⊆ B → B ⊆ C → A ⊆ C := by
  library_search

#print lema3
#print Set.Subset.trans
