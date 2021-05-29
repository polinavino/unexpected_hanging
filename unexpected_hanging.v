(* 
This formalization defines the axiom system which the unexpected hanging paradox informally describes.
Unsurprisingly, a reasonably defined notion of "surprise", when introduced into the system as one of 
the axioms, ie. one of the requirements of the hanging paradox system, introduces inconsistency.
 - surpriseIsWrong

Since we have proved False from the contradictory axioms, we can not prove anything about the system, 
including that the hanging happens on any day, and that it is a surprise. Hence, the prophecy is fulfilled.

We require the following to be true:
1. The hanging definitely happens, ie. here exists a day on which the hanging happens
  - hanging_definitely_happens
2. There is exactly one hanging that can happen
  - only_one_hanging
3. We always know for sure whether a hanging happened on a past day (or today) - we dont use this
to prove anything here
  - def_know_past

The SURPRISE is defined by requiring that we may prove that a hanging happens on a specific day 
only if that day is in the past (or today).

In order to ensure the possibility of surprise, we need to guarantee that there are at least 2 options 
for days on which the hanging can happen. So, we can re-state SURPRISE as MIN_TWO_OPTIONS
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

(* the proposition stating that it's not true that hanging happens on 
none of the weekdays *)
Definition hangingHappens := ~(forall d, ~hangingOnDay d).

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

(* we are surprised whenever :
IF the hanging did not yet happen up to and including today,
for every day that is after today,
proving that a hanging happens on a given day is not possible *)
(* that is, we cannot prove whether a hanging will happen on a specific future day *)
Definition SURPRISE := forall td : weekAndBefore, forall d,
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

(* SURPRISE implies that hanging can't be on friday *)
Definition noFri : SURPRISE -> ~ hangingOnDay friday. 
generalize hanging_definitely_happens.
compute. intros. elim H. intros.
assert (d=friday). 
generalize (only_one_hanging d H2 friday). compute. intros.
generalize (dayEqDec d friday). intros.
inversion H4. auto. tauto.
generalize (H0 (someWeekDay thursday) friday H1). tauto. 
Qed.

(* SURPRISE implies that hanging can't be on thursday *)
Definition noThurs : SURPRISE -> ~ hangingOnDay thursday. 
unfold SURPRISE.
intro S. generalize (noFri S). 
generalize hanging_definitely_happens.
compute. intros. elim H. intros. 
generalize (S (someWeekDay wednesday) d H2). intros.
apply H3. assert (d=thursday). 
generalize (only_one_hanging d H2 thursday). compute. intros.
generalize (dayEqDec d thursday). intros.
inversion H5. auto. tauto. rewrite H4. compute. tauto.
Qed.

(* SURPRISE implies that hanging can't be on wednesday *)
Definition noWed : SURPRISE -> ~ hangingOnDay wednesday. 
unfold SURPRISE.
intro S. generalize (noFri S). generalize (noThurs S). 
generalize hanging_definitely_happens.
compute. intros. elim H. intros. 
generalize (S (someWeekDay tuesday) d H3). intros.
apply H4. assert (d=wednesday). 
generalize (only_one_hanging d H3 wednesday). compute. intros.
generalize (dayEqDec d wednesday). intros.
inversion H6. auto. tauto. rewrite H5. compute. tauto.
Qed.

(* SURPRISE implies that hanging can't be on tuesday *)
Definition noTue : SURPRISE -> ~ hangingOnDay tuesday. 
unfold SURPRISE.
intro S. generalize (noFri S). generalize (noThurs S). generalize (noWed S). 
generalize hanging_definitely_happens.
compute. intros. elim H. intros. 
generalize (S (someWeekDay monday) d H4). intros.
apply H5. assert (d=tuesday). 
generalize (only_one_hanging d H4 tuesday). compute. intros.
generalize (dayEqDec d tuesday). intros.
inversion H7. auto. tauto. rewrite H6. compute. tauto.
Qed.

(* SURPRISE implies that hanging can't be on monday *)
Definition noMon : SURPRISE -> ~ hangingOnDay monday. 
unfold SURPRISE.
intro S. generalize (noFri S). generalize (noThurs S). generalize (noWed S). generalize (noTue S). 
generalize hanging_definitely_happens.
compute. intros. elim H. intros. 
generalize (S dayBefore d H5). intros.
apply H6. assert (d=monday). 
generalize (only_one_hanging d H5 monday). compute. intros.
generalize (dayEqDec d monday). intros.
inversion H8. auto. tauto. rewrite H7. compute. tauto.
Qed.

(* SURPRISE is inconsistent *) 
Definition surpriseIsWrong : ~SURPRISE.
intro S.
generalize (noFri S). generalize (noThurs S). generalize (noWed S). generalize (noTue S). generalize (noMon S).
generalize hanging_definitely_happens. 
unfold hangingHappens. intros. elim H. intro x. destruct x; tauto.
Qed.

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
(* if hanging didnt happen by thursday, it happens on friday *)
Definition defFri : noHangingYet (someWeekDay thursday) <-> hangingOnDay friday. 
generalize hanging_definitely_happens.
compute. split. 
intros. 


intros. apply H1. 
generalize (dayEqDec d friday). intro. inversion H3.
rewrite H4. auto.
generalize (only_one_hanging d H2 friday). compute. intros.
generalize (H5 H4 H0). tauto. i

ntros. apply H6.
generalize (H0 d).
rewrite H3. rewrite H3 in H1. intros. apply H. tauto.
apply H0.
generalize H1. destruct x; auto. generalize (H0 monday). tauto.
generalize (H0 tuesday). tauto.
 generalize (H0 wednesday). tauto.
 generalize (H0 thursday). tauto.
intros. apply H1.
generalize (only_one_hanging d H2 friday). compute. intros.
generalize (dayEqDec d friday). intro.
inversion H4. rewrite H5. auto. compute in H5.
generalize (H3 H5 H0). tauto. 
Qed. *)

(* always know if a hanging happened already or not *) 
(*
Definition defKnowPast : forall td, forall d, hangingOnDay d -> isBefore td d -> noHangingYet td.*)

(* 
if we exclude EITHER
- that today is thursday, OR
- that the hanging is on friday
we get that
if the hanging is provably on day d, 
that day must be today or before today
This is a consistent version of the definition of surprise
*)
(*
Definition allgoodBeforeThurs : forall td : weekAndBefore, forall d,
  (d <> friday \/ (td <> someWeekDay thursday)) ->
  (hangingOnDay d -> ~(isBefore td d)).

intros. intro. 
generalize (notBefore td d H0 H1). intros. generalize H1.
generalize (hanging_definitely_happens). unfold hangingHappens. intros.
intros. apply H3. intros. generalize (only_one_hanging d H0 d0). intros.
generalize (dayEqDec d d0). intros. inversion H6; auto.
intros. intro.

generalize hanging_definitely_happens.
compute. intros. elim H. intros.
assert (d=friday). 
generalize (only_one_hanging d H2 friday). compute. intros.
generalize (dayEqDec d friday). intros.
inversion H4. auto. tauto.
generalize (H0 (someWeekDay thursday) friday H1). tauto.  *)

