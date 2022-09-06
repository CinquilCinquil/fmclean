
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros h h2,
  apply h2,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  sorry, --sub_demonstração!!!!!!!!!!
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  sorry, --só um dos lados :(
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------
-- this might be useful: apply or.inl

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h with hp hq, 
  right, exact hp,
  left, exact hq,

end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h,
  split,
  exact h_right,
  exact h_left,

end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros h h2,
  cases h with c1 c2,
  contradiction,
  exact c2,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros h h2,
  cases h with c1 c2,
  contradiction,
  exact c2,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros h h2 h3,
  have hq : Q := h h3,
  apply h2,
  assumption,
  --contradiction tbm


end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h,
  intro h2,
  --sub_demonstração ???????????????
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intros h h2 h3,
  have hq : Q := h h3,
  contradiction,
  intro h,
  intro h2,
  --sub_demonstração ???????????????
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  have h2 : P∨¬P,
    right,
    intro h3,
    have h4 : P∨¬P,
      left,
      assumption,
    apply h h4,
    apply h h2,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros h h2,
  --sub_demonstração ???????????????
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros h h2,
  cases h2,
  cases h,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros h h2,
  cases h,
  cases h2,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro h_1,
  have h1 : P∨Q,
    left,
    assumption,
  contradiction,
  intro h_1,
  have h1 : P∨Q,
    right,
    assumption,
  contradiction,

end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros h1 h2,
  cases h1,
  cases h2,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  --sub_demonstração ???????????????
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros h1 h2,
  cases h2,
  cases h1,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro h,
  --sub_demonstração ???????????????
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro h,
  split,
  intro h1,
  have Q : P∨Q,
    left,
    assumption,
  contradiction,
  intro h1,
  have Q : P∨Q,
    right,
    assumption,
  contradiction,
  intros h h2,
  cases h,
  cases h2,
  contradiction,
  contradiction,

end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h,
  cases h_right,
  left,
  split,
  assumption,
  assumption,
  right,
  split,
  assumption,
  assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h,
  cases h,
  split,
  assumption,
  left,
  assumption,
  cases h,
  split,
  assumption,
  right,
  assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h,
  split,
  left,
  assumption,
  left,
  assumption,
  cases h,
  split,
  right,
  assumption,
  right,
  assumption,

end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h,
  cases h_left,
  cases h_right,
  left,
  assumption,
  left,
  assumption,
  cases h_right,
  left,
  assumption,
  right,
  split,
  assumption,
  assumption,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros h h2 h3,
  have hq : P∧Q,
    split,
    assumption,
    assumption,
  apply h,
  assumption,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h h1,
  cases h1,
  apply h,
  assumption,
  assumption, --tendi n ;-;

end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro h,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro h,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro h,
  right,
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  cases h,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro h,
  cases h,
  assumption,
  intro h,
  split,
  assumption,
  assumption,

end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro h,
  cases h,
  assumption,
  assumption,
  intro h,
  right,
  assumption,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro a,
  -- ??????????????????? tafuck do i do
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros h h2,
  cases h2 with a ha,
  have hq : ¬P a := h a,
  contradiction,

end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  -- ??????????????????? tafuck do i do
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h,
  cases h with a ha,
  intro a2,
  have hq : P a := a2 a,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro h,
  -- ??????????????????? tafuck do i do
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro h,
  intro a,
  -- ??????????????????? tafuck do i do
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros h h2,
  cases h with a ha,
  have hq : ¬P a := h2 a,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros h h2,
  cases h2 with a ha,
  have hq: P a := h a,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h,
  intro a,
  -- ??????????????????? tafuck do i do
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h,
  -- ??????????????????? tafuck do i do
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intros h h2,
  cases h2 with a ha,
  have hq: P a := h a,
  contradiction,
  intro h,
  intro a,
  -- ??????????????????? tafuck do i do
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  intros h h2,
  cases h with a ha,
  have hq: ¬P a := h2 a,
  contradiction,
  intro h,
  -- ??????????????????? tafuck do i do
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with a ha,
  cases ha,
  split,
  existsi a,
  assumption,
  existsi a,
  assumption,

end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with a ha,
  cases ha,
  left,
  existsi a,
  assumption,
  right,
  existsi a,
  assumption,

end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h,
  cases h with a ha,
  have hq : P a ∨ Q a,
    left,
    assumption,
  existsi a,
  assumption,
  cases h with a ha,
  have hq : P a ∨ Q a,
    right,
    assumption,
  existsi a,
  assumption,


end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro a,
  have hq: P a ∧ Q a := h a,
  cases hq,
  assumption,
  intro a,
  have hq: P a ∧ Q a := h a,
  cases hq,
  assumption,

end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  cases h,
  intro a,
  have hq: P a := h_left a,
  have hq2: Q a := h_right a,
  split,
  assumption,
  assumption,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  intro a,
  cases h,
  have hq: P a := h a,
  left,
  assumption,
  have hq: Q a := h a,
  right,
  assumption,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
