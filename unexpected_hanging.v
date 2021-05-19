(* 
This formalization defines the axiom system which the unexpected hanging paradox informally describes.
Unsurprisingly, a reasonably defined notion of "surprise", when introduced into the system as one of 
the axioms, ie. one of the requirements of the hanging paradox system, introduces inconsistency.

As a result, admitting the SURPRISE axiom allows us to prove everything (from False). 
The unexpected hanging situation is not a "paradox" so much as it is having contradictory 
requirements for the system to specify, making it inconsistent 

If we do not require to be surprised by a Friday hanging on Thursday, there is no 
inconsistency.
*) 

(* week days *)
Inductive weekDay : Type :=
  | monday : weekDay
  | tuesday : weekDay
  | wednesday : weekDay
  | thursday : weekDay
  | friday : weekDay.

(* a week day OR some day before the week starts,
the type used to specify a "today" *)
Inductive weekAndBefore : Type :=
  | dayBefore : weekAndBefore
  | someWeekDay : weekDay -> weekAndBefore.

(* hangingOnDay (d) means that hanging happened on day d *)
(* it means we know and can prove it happened on day d *)
Variable hangingOnDay : weekDay -> Prop.

(* the proposition stating that hanging happens on one of the weekdays *)
Definition hangingHappens : Prop. 
exact (exists d, (hangingOnDay d)).
Defined.

(* the predicate stating that hanging is not not happening on day d, ie. it can happen on d *)
Definition hangingCanBeOn := fun (d : weekDay) => (~~ (hangingOnDay d)).

(* this predicate says we can neither prove nor disprove that a hanging is on d *)
Definition cantProveOn := fun (d : weekDay) => (~ (hangingOnDay d \/ ~hangingOnDay d)).

(* if we cant prove either that hanging happens on d or that it doesnt happen,
hanging could happen on d *)
Definition proveCanBe : forall d, cantProveOn d -> hangingCanBeOn d.
intro. compute. tauto.
Qed.

(* is the day td before day d? *)
Fixpoint isBefore (td : weekAndBefore) (d : weekDay) : Prop :=
match td with
  | dayBefore => True
  | someWeekDay monday => match d with
      | monday => False
      | _ => True
    end
  | someWeekDay tuesday => match d with
      | monday => False
      | tuesday => False
      | _ => True
    end
  | someWeekDay wednesday => match d with
      | monday => False
      | tuesday => False
      | wednesday => False
      | _ => True
    end
  | someWeekDay thursday => match d with
      | monday => False
      | tuesday => False
      | wednesday => False
      | thursday => False
      | _ => True
    end
  | someWeekDay friday => match d with
      | _ => False
    end
end.

(* the hanging has not happened today or before *)
Definition noHangingYet := fun (td : weekAndBefore) => (forall d : weekDay, (~ isBefore td d) -> (~ hangingOnDay d)).

(* NOTE : Axioms are everything the person getting hanged KNOWS FOR SURE *)

(* the axiom stating hanging definitely happens on one of the weekdays *)
Axiom hanging_definitely_happens : hangingHappens.

(* if the hanging happens on day d, it does not happen on any other day *)
Axiom only_one_hanging : forall d : weekDay, (hangingOnDay d) -> (forall d' : weekDay, (d <> d') -> ~ (hangingOnDay d')).

(* for any day d, if today is after or on that day, we definitely know if the hanging happened on d or not *)
Axiom def_know_past : forall d : weekDay, forall td : weekAndBefore, 
  ~ (isBefore td d) -> (hangingOnDay d \/ ~ hangingOnDay d).

(* assuming that for any day d, if today is before that day, the hanging may happen on that day *)
Axiom def_maybe_future : forall td : weekAndBefore, noHangingYet td ->
  (forall d : weekDay, (isBefore td d) -> (hangingCanBeOn d)).

(* we are surprised whenever :
IF the hanging did not yet happen up to and including today,
for every day that is after today,
proving that a hanging happens on a given day is not possible *)
(* that is, we cannot prove whether a hanging will happen on a specific future day *)
Definition SURPRISE := forall td : weekAndBefore, 
  (noHangingYet td) -> forall d : weekDay, ((isBefore td d) -> ~(hangingOnDay d \/ ~ hangingOnDay d)).

(* If the hanging happens on d, it can happen on d *)
Definition doesImpCan : (weekDay -> Prop) -> Prop.
intro can. exact (forall d : weekDay, hangingOnDay d -> can d). Defined.

Definition doesImpCanPf : doesImpCan hangingCanBeOn.
unfold doesImpCan. intros. unfold hangingCanBeOn. tauto. Qed.

(* If the hanging does not happens on d, it cannot happen on d *)
Definition notDoesImpNotCan : (weekDay -> Prop) -> Prop.
intro can. exact (forall d : weekDay, ((~ (hangingOnDay d)) -> (~ (can d)))). Defined.

Definition notDoesImpNotCanPf : notDoesImpNotCan hangingCanBeOn.
unfold notDoesImpNotCan. intros. unfold hangingCanBeOn. tauto. Qed.

(* There is a day d such that if the hanging can happen on d, we can prove that it EITHER does OR does NOT happen on d *)
Definition canImpSomething := fun (can : weekDay -> Prop) => (exists d : weekDay, can d -> (hangingOnDay d \/ ~ hangingOnDay d)).

(* without law of excluded middle, we cannot prove (or disprove) this for can = hangingCanBeOn *)
(*
Definition canImpSomethingPf : canImpSomething hangingCanBeOn.
unfold hangingCanBeOn. unfold canImpSomething.  intro. elim H.
intros. tauto. 
*)

(* any predicate weekDay -> Prop that satisfies 
1. doesImpCan 
2. notDoesImpNotCan 
also states for each day, that hangingCanBeOn that day
ie. hangingCanBeOn is the weakest predicate satisfying these
*)
Definition canBeIsWeakest : forall can : weekDay -> Prop, (notDoesImpNotCan can /\ doesImpCan can) -> (forall d : weekDay, can d -> hangingCanBeOn d).
unfold notDoesImpNotCan. unfold doesImpCan. unfold hangingCanBeOn. intros. intros;
elim H; intros H1 H2. generalize (H1 d). tauto. Qed.

(* eq on days is decidable *)
Definition dayEqDec : forall x d : weekDay, (x=d \/ x<>d). 
destruct d, x; intuition discriminate.
Qed.

(* if hanging didnt happen by thursday, it happens on friday *)
Definition defFri : noHangingYet (someWeekDay thursday) <-> hangingOnDay friday. 
generalize hanging_definitely_happens.
compute. split. intros. elim H. intros.
generalize H1. destruct x; auto. generalize (H0 monday). tauto.
generalize (H0 tuesday). tauto.
 generalize (H0 wednesday). tauto.
 generalize (H0 thursday). tauto.
intros. apply H1.
generalize (only_one_hanging d H2 friday). compute. intros.
generalize (dayEqDec d friday). intro.
inversion H4. rewrite H5. auto. compute in H5.
generalize (H3 H5 H0). tauto. 
Qed.


(* Surprise implies that hanging must have already happened by thursday. *)
Definition byThurs : SURPRISE -> ~noHangingYet (someWeekDay thursday).
unfold SURPRISE. intros. intro.
generalize (H (someWeekDay thursday) H0 friday).
compute. intros. apply H1; auto.
Qed.

(* Surprise implies that hanging hanging cant ever be on friday *)
Definition noFri : SURPRISE -> ~hangingOnDay friday.
generalize byThurs. generalize defFri.
tauto.
Qed.

(* we know hanging CAN be on friday before we know when the hanging happens *) 
Definition surpriseIsWrong : ~SURPRISE.
generalize (def_maybe_future dayBefore).
intros. intro. generalize H. compute.
intros. 
assert ((forall d : weekDay, (True -> False) -> hangingOnDay d -> False)) as tf. intros. tauto.
generalize (H1 tf friday). intros.
generalize noFri. tauto.
Qed.

(* if 
- there has not been a hanging yet until today, 
- today is not thursday
we get that for every day that is 
- NOT friday,
- is after today,
we cannot prove whether a hanging happens on that day or not *)
Definition allgoodBeforeThurs : forall td : weekAndBefore,
 noHangingYet td ->
 forall d : weekDay, (d <> friday \/ (td <> someWeekDay thursday)) ->
 isBefore td d -> ~ (hangingOnDay d \/ ~ hangingOnDay d).
intros. generalize H1.
destruct d; destruct td; try (destruct w); inversion H0; try (compute; tauto); try (intro isb; clear isb).
intro. inversion H3.
generalize (def_maybe_future dayBefore H tuesday). compute. intro def_may.
generalize (only_one_hanging monday H4 tuesday). intro one_hang.
assert (~ hangingOnDay tuesday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay monday).
generalize (def_maybe_future dayBefore H monday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future dayBefore H tuesday). compute. intro def_may.
generalize (only_one_hanging monday H4 tuesday). intro one_hang.
assert (~ hangingOnDay tuesday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay monday).
generalize (def_maybe_future dayBefore H monday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future dayBefore H wednesday). compute. intro def_may.
generalize (only_one_hanging tuesday H4 wednesday). intro one_hang.
assert (~ hangingOnDay wednesday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay tuesday).
generalize (def_maybe_future dayBefore H tuesday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future dayBefore H wednesday). compute. intro def_may.
generalize (only_one_hanging tuesday H4 wednesday). intro one_hang.
assert (~ hangingOnDay wednesday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay tuesday).
generalize (def_maybe_future dayBefore H tuesday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay monday) H wednesday). compute. intro def_may.
generalize (only_one_hanging tuesday H4 wednesday). intro one_hang.
assert (~ hangingOnDay wednesday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay tuesday).
generalize (def_maybe_future (someWeekDay monday) H tuesday). compute. intro def_may.
 tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay monday) H wednesday). compute. intro def_may.
generalize (only_one_hanging tuesday H4 wednesday). intro one_hang.
assert (~ hangingOnDay wednesday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay tuesday).
generalize (def_maybe_future (someWeekDay monday) H tuesday). compute. intro def_may.
 tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future dayBefore H thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay wednesday).
generalize (def_maybe_future dayBefore H wednesday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future dayBefore H thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay wednesday).
generalize (def_maybe_future dayBefore H wednesday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay monday) H thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay wednesday).
generalize (def_maybe_future (someWeekDay monday) H wednesday). compute. intro def_may.
 tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay monday) H thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay wednesday).
generalize (def_maybe_future (someWeekDay monday) H wednesday). compute. intro def_may.
 tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay tuesday) H thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay wednesday).
generalize (def_maybe_future (someWeekDay tuesday) H wednesday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay tuesday) H thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay wednesday).
generalize (def_maybe_future (someWeekDay tuesday) H wednesday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future dayBefore H friday). compute. intro def_may.
generalize (only_one_hanging thursday H4 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay thursday).
generalize (def_maybe_future dayBefore H thursday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future dayBefore H friday). compute. intro def_may.
generalize (only_one_hanging thursday H4 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay thursday).
generalize (def_maybe_future dayBefore H thursday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay monday) H friday). compute. intro def_may.
generalize (only_one_hanging thursday H4 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay thursday).
generalize (def_maybe_future (someWeekDay monday) H thursday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay monday) H friday). compute. intro def_may.
generalize (only_one_hanging thursday H4 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay thursday).
generalize (def_maybe_future (someWeekDay monday) H thursday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay tuesday) H friday). compute. intro def_may.
generalize (only_one_hanging thursday H4 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay thursday).
generalize (def_maybe_future (someWeekDay tuesday) H thursday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay tuesday) H friday). compute. intro def_may.
generalize (only_one_hanging thursday H4 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay thursday).
generalize (def_maybe_future (someWeekDay tuesday) H thursday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay wednesday) H friday). compute. intro def_may.
generalize (only_one_hanging thursday H4 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay thursday).
generalize (def_maybe_future (someWeekDay wednesday) H thursday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay wednesday) H friday). compute. intro def_may.
generalize (only_one_hanging thursday H4 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay thursday).
generalize (def_maybe_future (someWeekDay wednesday) H thursday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future dayBefore H thursday). compute. intro def_may.
generalize (only_one_hanging friday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay friday).
generalize (def_maybe_future dayBefore H friday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay monday) H thursday). compute. intro def_may.
generalize (only_one_hanging friday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay friday).
generalize (def_maybe_future (someWeekDay monday) H friday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay tuesday) H thursday). compute. intro def_may.
generalize (only_one_hanging friday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay friday).
generalize (def_maybe_future (someWeekDay tuesday) H friday). compute. intro def_may. tauto. tauto.

intro. inversion H3.
generalize (def_maybe_future (someWeekDay wednesday) H thursday). compute. intro def_may.
generalize (only_one_hanging friday H4 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
assert (~~ hangingOnDay friday).
generalize (def_maybe_future (someWeekDay wednesday) H friday). compute. intro def_may. tauto. tauto.
Qed.
