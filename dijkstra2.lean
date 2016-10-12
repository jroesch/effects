namespace pure
  def {w u v} context (A : Type w) (E : Type u) := (A → Type v) -> E

  def pure {A T : Type} (x : T) : context A T :=
    fun y, x
  
  def apply {A T U : Type}
    (l : context A (T -> U))
    (r : context A T) : context A U :=
    fun p, l p (r p)

  def push {A T U : Type} (f : (T → context A U)) : context A (T -> U) :=
    fun p e1, f e1 p

  @[reducible] def {u} wp (A : Type u) := context A Prop
  
  def return_wp {A : Type} (x : A) : wp A :=
    fun p, p x

  def bind_wp (A B : Type) (wp1 : wp A) (wp2 : A → wp B) : wp B :=
    fun p, wp1 (fun (x : A), wp2 x p)

  def strengthen (A : Type) (wp1 : wp A) (wp2 : wp A) :=
    forall (p1 p2 : A → Prop), (forall x, p1 x -> p2 x) -> (wp1 p1 -> wp2 p2)
end pure

constant PURE (T : Type) (wp : pure.wp T) : Type

noncomputable def Pure (A : Type) (pre : Prop) (post : A -> Prop) : Type :=
    PURE A (fun (p : A → Prop), pre ∧ (forall (x : A), post x → p x))

def returnP {A : Type} (x : A) : PURE A (pure.return_wp x) :=
begin
  tactic.unfold [`pure.return_wp],
end

definition sqrt' (x : nat) : PURE nat (fun (post : nat → Prop), forall y, y >= 0 → post y) := sorry

def weaken :
  forall (p q : pure.wp nat), (forall post, p post -> q post) -> PURE nat p -> PURE nat q :=
begin
  intros,
end

definition sqrt (x : nat) : Pure nat true (fun y, y >= 0) :=
begin
  tactic.unfold [`Pure],
  apply sqrt',
end

def test (n : nat) : Pure nat (n > 0) (fun m, m = n) :=
begin
  tactic.unfold [`Pure]
end
