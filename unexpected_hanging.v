(* week days *)
Inductive weekDay : Type :=
  | monday : weekDay
  | tuesday : weekDay
  | wednesday : weekDay
  | thursday : weekDay
  | friday : weekDay.

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

(* we are surprised whenever
- IF we are only able to prove whether a hanging DID or DID NOT happen, 
the day on which it happened has already passed *)
(* that is, we cannot prove whether a hanging will happen on a specific future day *)
Definition SURPRISE := forall td : weekAndBefore, forall d : weekDay,
  (hangingOnDay d \/ ~ hangingOnDay d) -> ~ isBefore td d.

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

(* if hanging didnt happen by thursday, it happens on friday *)
Definition defFri : noHangingYet (someWeekDay thursday) -> hangingOnDay friday.
generalize hanging_definitely_happens.
compute. intros. elim H. intros.
generalize H1. destruct x; auto. generalize (H0 monday). tauto.
generalize (H0 tuesday). tauto.
 generalize (H0 wednesday). tauto.
 generalize (H0 thursday). tauto.
Qed.

(* SURPRISE definition fails thursday *)
Definition thursdayIsInconsisten : ~(hangingOnDay friday \/ ~ hangingOnDay friday -> ~ isBefore (someWeekDay thursday) friday).
generalize defFri. intro defFri.
compute. intros. apply H; auto.
Qed.

(* this definition of surprise is inconsistent, and so implies False *)
Definition surpriseIsInconsisten : ~SURPRISE.
unfold SURPRISE.  
intro. 
generalize (H (someWeekDay thursday) friday).
exact thursdayIsInconsisten. 
Qed. 


(* if we dont require to be surprised by a Friday hanging (we know on Thursday that it'll happen Friday), surprise is consistent *)
Definition noThursSurprise : forall td : weekAndBefore, forall d : weekDay, td <> someWeekDay thursday <->
  (hangingOnDay d \/ ~ hangingOnDay d -> ~ isBefore td d).
intros. split; intros. intro. 
generalize (def_know_past d td). intro know_past.
generalize (def_maybe_future td). unfold hangingCanBeOn. intro may_future. 
generalize (only_one_hanging d). intro one_hang. 
generalize (hanging_definitely_happens). compute. intro. elim H2. intro x. intro def_hap. 
generalize H1. destruct d; compute; intro; auto.
assert (noHangingYet dayBefore ). compute. intros. tauto. 
generalize (may_future H4 monday H1). 
destruct H0; try tauto. generalize (one_hang H0 tuesday). intros.
generalize (may_future H4 tuesday). compute. intros.
assert (~ hangingOnDay tuesday). assert (monday <> tuesday). compute. intro t. inversion t. exact (H5 H8).
tauto.
assert (noHangingYet dayBefore ). compute. intros. tauto. 
generalize (may_future H4 tuesday H1). 
destruct H0; try tauto. generalize (one_hang H0 wednesday). intros.
generalize (may_future H4 wednesday). compute. intros.
assert (~ hangingOnDay wednesday). assert (tuesday <> wednesday). compute. intro t. inversion t. exact (H5 H8).
tauto.
assert (noHangingYet dayBefore ). compute. intros. tauto. 
generalize (may_future H4 wednesday H1). 
destruct H0; try tauto. generalize (one_hang H0 thursday). intros.
generalize (may_future H4 thursday). compute. intros.
assert (~ hangingOnDay thursday). assert (wednesday <> thursday). compute. intro t. inversion t. exact (H5 H8).
tauto.
assert (noHangingYet dayBefore ). compute. intros. tauto. 
generalize (may_future H4 thursday H1). 
destruct H0; try tauto. generalize (one_hang H0 friday). intros.
generalize (may_future H4 friday). compute. intros.
assert (~ hangingOnDay friday). assert (thursday <> friday). compute. intro t. inversion t. exact (H5 H8).
tauto. 
assert (noHangingYet dayBefore). compute. intros. tauto.
destruct H0. 
ssert (~~ hangingOnDay friday). exact (may_future H4 friday H1).
generalize thursdayIsInconsisten. compute.
intros. apply H4. intro. tauto.
 tauto. intros.
Focus 3.
assert ((SURPRISE (someWeekDay thursday) friday) -> False).
generalize surpriseIsInconsisten. unfold SURPRISE. intro. apply H4. compute. intros.
 generalize (H5 (someWeekDay thursday)). 
assert (noHangingYet dayBefore ). compute. intros. tauto. 
generalize (may_future H4 thursday H1). 
destruct H0; try tauto. generalize (one_hang H0 friday). intros.
generalize (may_future H4 friday). compute. intros.
assert (~ hangingOnDay friday). assert (thursday <> friday). compute. intro t. inversion t. exact (H5 H8).
tauto.

 tauto.
assert (
compute in H4. intro. generalize (H4 monday). intro. try tauto.
intros.
compute. generalize (H4 H0). intros.

compute. intro. elim H6. intro.
Focus 2.
generalize (dayEqDec x d). intro. generalize H0.
inversion H7.
 tauto.
 tauto.
destruct td; destruct d; compute; try (intro fl; inversion fl).

try (inversion H). destruct H.

(* if the hanging is not on Friday, surprise is consistent *)
Definition noFriHanging : forall td : weekAndBefore, forall d : weekDay, d <> friday <->
  (hangingOnDay d \/ ~ hangingOnDay d -> ~ isBefore td d).
