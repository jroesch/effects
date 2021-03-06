constant PURE (T : Type) (wp wlp : (T → Prop) → Prop) : Type

namespace pure
  def post (A : Type) := A → Prop
  @[reducible] def pre := Prop
  def wp (A : Type) := post A → pre

  def return_type (A : Type) (x : A) :=
    fun (p : post A), p x
end pure

noncomputable def Pure (A : Type) (pre : Prop) (post : A -> Prop) :=
  PURE A (fun (p : pure.post A), pre /\ forall (x : A), post x -> p x)
         (fun (p : pure.post A), forall (x : A), pre /\ post x -> p x)

definition return_PURE (A : Type) (x : A) :=
  fun (p : pure.post A), p x
  
definition bind_PURE {A B : Type}
  (wp1: pure.wp A)
  (wp2: A → pure.wp B) : pure.wp B :=
  fun (post : pure.post B), wp1 (fun (x : A), wp2 x post)
  
constant assert (p : Prop) : Pure unit p (fun x, p)

constant returnPure {A : Type} (x : A) : PURE A (return_PURE A x) (return_PURE A x)

constant bindPure {A B : Type} :
forall (wp wlp : pure.wp A)
       (wp' wlp' : A -> pure.wp B)
       (e1 : PURE A wp wlp) (e2 : forall (x : A), PURE B (wp' x) (wlp' x)),
       PURE B (bind_PURE wp wp') (bind_PURE wlp wlp')

  
def as_requires {A : Type} (wp : pure.wp A) := wp (fun x, true)
def as_ensures  {A : Type} (wlp : pure.wp A) (x : A) := not (wlp (fun y, not (y = x)))

lemma Pure_f :
  forall T wp wp' wlp wlp',
    wp = wp' ->
    wlp = wlp' ->
    PURE T wp wlp ->
    PURE T wp' wlp' := sorry

def as_Pure (A : Type) (B : A -> Type)
 (wp : (forall x : A, pure.wp (B x)))
 (wlp : (forall x : A, pure.wp (B x)))
 (f : (forall x : A, PURE (B x) (wp x) (wlp x)))
 (x : A) : Pure (B x) (as_requires (wp x)) (as_ensures (wlp x)) :=
begin
  tactic.unfold [`Pure, `as_requires, `as_ensures],
  apply Pure_f,
  tactic.rotate_left 2,
  apply f,
  apply funext,
  intros,
  apply sorry,
  apply sorry,
end

def foo : forall x, Pure nat (x > 0) (fun y, y = x) := do
  tactic.refine (fun x, as_Pure (bindPure _ _ _ _ (assert (x > 0)) (returnPure x)))
  

-- def gt_zero (n : nat) : Pure nat (0 < n) (fun n', n' > 0) :=
--    returnPure n

-- example (x : nat) : PURE nat
-- (fun p', x > 0 /\ p' (x + 1))
-- (fun p', x > 0 -> p' (x + 1)) := sorry
