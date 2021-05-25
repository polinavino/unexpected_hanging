(* 
This formalization defines the axiom system which the unexpected hanging paradox informally describes.
Unsurprisingly, a reasonably defined notion of "surprise", when introduced into the system as one of 
the axioms, ie. one of the requirements of the hanging paradox system, introduces inconsistency.

We start by defining SURPRISE as a requirement to be surprised by a hanging on every day 
of the week, including being surprised on Thursday by a Friday hanging. This 
is False, and thus this SURPRISE requirement introduces a contradiction, ie. proves False.
From False, we can prove anything - 
including that the hanging happened on one of the days!

Now, the paradox does not require that the hanging necessarily be a surprise on *every* week day,
only that it is a surprise when it does happen. That is, on the days surprise is not possible,
such a Friday, the hanging will not happen. We can thus construct an updated definition of surprise
that excludes the hanging from being on days on which surprise is not possible. 

We do not know ahead of time which days those are, but it does not matter. We show that 
if we take *any* of the subsets (of hanging days) that were considered by the hangee
(ie. Mon-Fri, Mon-Thurs, Mon-Wed, etc.), and require to be surprised only by hangings 
on those days. Since we know it is necessary 
that 
- the hanging happens, and 
- it is a surprise, 
such a selected-day definition of surprise can still be shown to introduces inconsistency.

There is also the following sanity check : allgoodBeforeThursday.
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

(* week days *)
Inductive chooseDays : Type :=
  | allDays : chooseDays
  | tilFri : chooseDays
  | tilThurs : chooseDays
  | tilWed : chooseDays
  | tilTue : chooseDays
  | tilMon : chooseDays.

Fixpoint apl (cd : chooseDays) (d : weekDay) : Prop :=
match cd with
  | allDays => match d with
      | monday => False
      | _ => True
    end
  | tilFri => match d with
      | friday => False
      | _ => True
    end
  | tilThurs => match d with
      | thursday => False
      | friday => False
      | _ => True
    end
  | tilWed => match d with
      | wednesday => False
      | thursday => False
      | friday => False
      | _ => True
    end
  | tilTue => match d with
      | tuesday => False
      | wednesday => False
      | thursday => False
      | friday => False
      | _ => True
    end
  | tilMon => match d with
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
Definition SURPRISE := forall td : weekAndBefore, forall d,
  hangingOnDay d -> ~(isBefore td d).

(* given any subset of week days on which surprise will hold (and thus hanging is possible),
restrict a definition of surprise to only those days *)
Definition SOME_DAYS_SURPRISE := forall (someDays : chooseDays), 
  forall td : weekAndBefore, forall d, apl someDays d ->
  hangingOnDay d -> ~(isBefore td d).

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

(* if hanging didnt happen by thursday, it happens on friday *)
Definition noFri : SURPRISE -> ~ hangingOnDay friday. 
generalize hanging_definitely_happens.
compute. intros. elim H. intros.
generalize (H0 (someWeekDay thursday) x H2). 
intros. apply H3. 
assert (x=friday). 
generalize (only_one_hanging x H2 friday). compute. intros.
generalize (dayEqDec x friday). intros.
inversion H5. auto. tauto. rewrite H4. tauto.
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

(* surprise definition that restricts hanging days to only some days,
including to only the surprise-possible days, is also inconsistent *)
(*
Definition someDaysSupriseIsWrong : ~SOME_DAYS_SURPRISE.
unfold SOME_DAYS_SURPRISE.
prove this!
*)

(* if a hanging is on day d, and today is before that day, then no hanging happened yet *)
Definition notBefore : forall td, forall d, hangingOnDay d -> isBefore td d -> noHangingYet td.
intros.
destruct td.
compute. tauto.
unfold noHangingYet. intros. intro.
generalize (only_one_hanging d H d0). intros.
generalize (dayEqDec d d0). intros.
inversion H4. 
apply H1. rewrite <- H5. tauto. tauto.
Qed.

(* 
if we exclude EITHER
- that today is thursday, OR
- that the hanging is on friday
we get that
if the hanging is provably on day d, 
that day must be today or before today
This is a consistent version of the definition of surprise
*)
Definition allgoodBeforeThurs : forall td : weekAndBefore, forall d,
  (d <> friday \/ (td <> someWeekDay thursday)) ->
  (hangingOnDay d -> ~(isBefore td d)).

intros. intro. 
generalize (notBefore td d H0 H1). intros. generalize H1.

destruct d; destruct td; try (destruct w); inversion H; try (compute; tauto); try (intro isb; clear isb).
generalize (def_maybe_future dayBefore H2 tuesday). compute. intro def_may.
generalize (only_one_hanging monday H0 tuesday). intro one_hang.
assert (~ hangingOnDay tuesday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future dayBefore H2 tuesday). compute. intro def_may.
generalize (only_one_hanging monday H0 tuesday). intro one_hang.
assert (~ hangingOnDay tuesday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future dayBefore H2 wednesday). compute. intro def_may.
generalize (only_one_hanging tuesday H0 wednesday). intro one_hang.
assert (~ hangingOnDay wednesday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future dayBefore H2 wednesday). compute. intro def_may.
generalize (only_one_hanging tuesday H0 wednesday). intro one_hang.
assert (~ hangingOnDay wednesday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay monday) H2 wednesday). compute. intro def_may.
generalize (only_one_hanging tuesday H0 wednesday). intro one_hang.
assert (~ hangingOnDay wednesday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay monday) H2 wednesday). compute. intro def_may.
generalize (only_one_hanging tuesday H0 wednesday). intro one_hang.
assert (~ hangingOnDay wednesday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future dayBefore H2 thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future dayBefore H2 thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay monday) H2 thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay monday) H2 thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay tuesday) H2 thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay tuesday) H2 thursday). compute. intro def_may.
generalize (only_one_hanging wednesday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future dayBefore H2 friday). compute. intro def_may.
generalize (only_one_hanging thursday H0 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future dayBefore H2 friday). compute. intro def_may.
generalize (only_one_hanging thursday H0 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay monday) H2 friday). compute. intro def_may.
generalize (only_one_hanging thursday H0 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay monday) H2 friday). compute. intro def_may.
generalize (only_one_hanging thursday H0 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay tuesday) H2 friday). compute. intro def_may.
generalize (only_one_hanging thursday H0 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay tuesday) H2 friday). compute. intro def_may.
generalize (only_one_hanging thursday H0 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay wednesday) H2 friday). compute. intro def_may.
generalize (only_one_hanging thursday H0 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay wednesday) H2 friday). compute. intro def_may.
generalize (only_one_hanging thursday H0 friday). intro one_hang.
assert (~ hangingOnDay friday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future dayBefore H2 thursday). compute. intro def_may.
generalize (only_one_hanging friday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay monday) H2 thursday). compute. intro def_may.
generalize (only_one_hanging friday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay tuesday) H2 thursday). compute. intro def_may.
generalize (only_one_hanging friday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.

generalize (def_maybe_future (someWeekDay wednesday) H2 thursday). compute. intro def_may.
generalize (only_one_hanging friday H0 thursday). intro one_hang.
assert (~ hangingOnDay thursday). apply one_hang. compute. intro ne; inversion ne. tauto.
Qed.
