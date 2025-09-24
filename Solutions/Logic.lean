section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hp hnp
  contradiction


theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro nnp
  by_cases p : P
  . exact p
  . have boom : False := nnp p
    exfalso
    exact boom

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  . apply doubleneg_elim
  . apply doubleneg_intro


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro pq
  rcases pq with (p | q)
  . right
    exact p
  . left
    exact q

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro pq
  rcases pq with ⟨p, q⟩
  constructor
  . exact q
  . exact p


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro npq
  intro p
  rcases npq with (np | q)
  . contradiction -- We have P → ⊥ and we have p
  . exact q

theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro pq
  intro np
  rcases pq with (p | q)
  . contradiction -- We have P and we have P → ⊥
  . exact q


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro piq nq p
  have q := piq p
  -- have boom := nq q can simply be ommited
  contradiction

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro nqinp p
  by_cases q : Q
  . exact q
  . have np := nqinp q
    contradiction

theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  . apply impl_as_contrapositive
  . apply impl_as_contrapositive_converse


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro lem
  have ponp : P ∨ ¬ P := by
    right
    intro p
    have ponp' : P ∨ ¬ P := by
      left
      exact p
    have boom := lem ponp'
    exact boom -- Podiamos substituir essas duas linhas simplesmente por contradiction 
  contradiction -- Esse contradicion faz a mesma coisa das duas linhas anteriores

------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro pqip np
  have pq : (P → Q) := by
    apply impl_as_contrapositive_converse
    intro nq p
    contradiction
  have boom := np (pqip pq)
  contradiction


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases hp : P
  . right
    intro q
    exact hp
  . left
    intro p
    contradiction


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro poq npanq
  rcases npanq with ⟨np, nq⟩
  rcases poq with (p | q)
  . contradiction
  . contradiction

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro paq nponq
  rcases paq with ⟨p, q⟩
  rcases nponq with (np | nq)
  . contradiction
  . contradiction


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro npoq
  constructor
  . intro p
    apply npoq
    . left
      exact p
  . intro q
    apply npoq
    . right
      exact q

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro npaq poq
  have ⟨np, nq⟩ := npaq
  rcases poq with (p | q)
  . contradiction
  . contradiction

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro npaq
  by_cases p : P
  . left
    intro q
    have boom := npaq ⟨p, q⟩
    exact boom
  . right
    exact p

theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro nqonp paq
  have ⟨p, q⟩ := paq
  rcases nqonp with (nq | np)
  . contradiction
  . contradiction

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  . apply demorgan_conj
  . apply demorgan_conj_converse

theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  . apply demorgan_disj
  . apply demorgan_disj_converse


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro paqr
  have ⟨p, qor⟩ := paqr
  rcases qor with (q | r)
  . left
    constructor
    . exact p
    . exact q
  . right
    exact ⟨p, r⟩ -- Equivalente a demonstrar p e depois demonstrar r com o constructor

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro pqopr
  constructor
  . rcases pqopr with (pq | pr)
    . exact pq.left
    . exact pr.left
  . rcases pqopr with (pq | pr)
    . left
      exact pq.right
    . right
      exact pr.right

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro poqr
  rcases poqr with (p | qr)
  . constructor
    . left
      exact p
    . left
      exact p
  . constructor
    . right
      exact qr.left
    . right
      exact qr.right

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro ⟨pq, pr⟩  
  rcases pq with (p | q)
  . left
    exact p
  . rcases pr with (p | r)
    . left
      exact p
    . right
      exact ⟨q, r⟩

------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro pqir p q
  have r := pqir ⟨p, q⟩
  exact r

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro piqr paq
  have ⟨p, q⟩ := paq
  have r := piqr p q
  exact r

------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro p
  exact p

------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro p
  left
  exact p

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro q
  right
  exact q

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro paq
  rcases paq with ⟨p, q⟩
  exact p

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro paq
  rcases paq with ⟨p, q⟩
  exact q

------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  . intro pop
    rcases pop with (p | p)
    . exact p
    . exact p
  . intro p
    left
    exact p

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  . intro pap
    rcases pap with ⟨p1, p2⟩
    exact p1
  . intro p
    constructor
    . exact p
    . exact p

------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro boom
  -- contradiction
  exfalso
  exact boom

theorem true_top :
  P → True  := by
  intro p
  trivial


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  intro h u pu
  apply h
  exists u

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  intro h he
  have ⟨u, pu⟩ := he
  apply h u
  exact pu

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  intro h
  apply doubleneg_elim
  intro nhe
  apply h
  intro x
  apply doubleneg_elim
  intro npx
  apply nhe
  exists x

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  intro he h
  have ⟨x, npx⟩ := he
  have px := h x
  contradiction

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  constructor
  . apply demorgan_forall
  . apply demorgan_forall_converse

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  constructor
  . apply demorgan_exists
  . apply demorgan_exists_converse


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
