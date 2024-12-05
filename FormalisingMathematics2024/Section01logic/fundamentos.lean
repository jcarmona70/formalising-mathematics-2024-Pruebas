import Mathlib.Tactic


-- ver: https://en.wikipedia.org/wiki/Hilbert_system

def my_true:= ∀ P:Prop, P → P

lemma my_true_def:my_true ↔ ∀ P:Prop, P → P:= by
  rfl

#print my_true

lemma obvio:my_true:= by
  intro P
  intro hP
  exact hP

axiom my_not:Prop → Prop

def PL1:= ∀ P Q:Prop, P → (Q → P)

lemma p1:PL1:= by
  intro P
  intro Q
  intro hP
  intro hQ
  exact hP

def PL2:= ∀ P Q R:Prop, (P → (Q → R)) → ((P → Q) → (P → R))

lemma pl2:PL2:= by
  intro P
  intro Q
  intro R
  intro h1
  intro h2
  intro h3
  exact h1 h3 (h2 h3)

def PL3:= ∀ P Q:Prop, my_not P → (P → Q)

def PL3i:= ∀ P :Prop, (P → my_not P) → my_not P

def PL4:= ∀ P:Prop,  ((my_not P) → P) → P

def my_false := my_not my_true

lemma my_false_def:my_false ↔ my_not my_true:= by
  rfl

lemma caract_my_false :PL3 → (∀ P:Prop, my_false → P):= by
  intro pl3
  intro P
  intro h
  rw [my_false_def] at h
  rw [my_true_def] at h
  have cosa:= pl3  my_true P
  have cosa1:= cosa h
  have hyp := obvio
  apply cosa1
  exact hyp


lemma caract_not (pl3:PL3) (pl3i:PL3i):∀ P:Prop, (my_not P) ↔ (P → my_false):= by
  intro P
  constructor
  exact pl3 P my_false
  intro implic
  have h:=caract_my_false pl3 (my_not P)
  have h1: P → my_not P:= by
    intro h2
    exact h (implic h2)
  exact pl3i P h1






#print PL1
