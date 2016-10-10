constant PURE (T : Type) (wp wlp : (T → Prop) → Prop) : Type

namespace pure
  def post (A : Type) := A → Prop
  def pre := Prop
  def wp (A : Type) := post A → pre

  def return_type (A : Type) (x : A) :=
    fun (p : post A), p x
end pure

noncomputable def Pure (A : Type) (pre : Prop) (post : A -> Prop) :=
  PURE A (fun (p : pure.post A), pre /\ forall (x : A), post x -> p x)
         (fun (p : pure.post A), forall (x : A), pre /\ post x -> p x)

definition return_PURE (A : Type) (x : A) :=
  fun (p : pure.post A), p x

constant returnPure {A : Type} (x : A) : PURE A (return_PURE A x) (return_PURE A x)

def as_requires {A : Type} (wp : pure.wp A) := wp (fun x, true)
def as_ensures  {A : Type} (wlp : pure.wp A) (x : A) := not (wlp (fun y, not (y = x)))

def as_Pure (A : Type) (B : A -> Type)
 (wp : (forall x : A, pure.wp (B x)))
 (wlp : (forall x : A, pure.wp (B x)))
 (f : (forall x : A, PURE (B x) (wp x) (wlp x)))
 (x : A) : Pure (B x) (as_requires (wp x)) (as_ensures (wlp x)) := sorry

example : (as_Pure nat (fun x, nat) (return_PURE nat) (return_PURE nat)) == true :=
begin
end



def gt_zero (n : nat) : Pure nat (0 < n) (fun n', n' > 0) :=
   returnPure n

example (x : nat) : PURE nat
(fun p', x > 0 /\ p' (x + 1))
(fun p', x > 0 -> p' (x + 1)) := sorry
