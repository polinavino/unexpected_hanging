(* 
This formalization defines the axiom system which the unexpected hanging paradox informally describes.
We do this by adding axioms to a system of constructive logci.
Axiom are statements assumed to be true within the system without a proof.

We describe the system using in first-order constructive logic, with predicates 
quantified over elements (in this case, weekdays). No special constructors are added 
to expand our logic.

There is no special model for knowledge that we introduce - in accordance with constructive logic,
we only know for sure the things we can prove (with the
exception of axioms we include as part of the definition of our system). If we introduce
axioms of the flavour "proving X introduces an inconsistency/contradiction", or an axiom from 
which we can conclude this, we are now restricted in introducing certain additional 
axioms to the system. In particular, adding other 
axioms from which we can conclude X makes our system inconsistent. 

To describe the system, we introduce the following axioms, which represent the rules 
of the execution :
1. hanging_definitely_happens : 
   The hanging definitely happens on one of the days, 
   ie. if we prove that for all days, the hanging did not happen,
   we arrive at a contradiction
   
2. only_one_hanging :
   There is exactly one hanging that can happen

The notion of surprise, as interpreted by the person being hanged,
leads them to reason that there is no day on which the hanging can happen.
Unsurprisingly (in accordance with the original description of the paradox), admitting this notion of 
surprise as one of the axioms introduces inconsistency. As in the informal description, 
we are able to conclude that the hanging cannot occur if we accept this definition of 
surprise.

We call this notion of suprise SURPRISED_ALWAYS, and prove its inconsistency in the Theorem :
  - surpriseIsWrong

We also give an alternate notion of surprise, SURPRISED_SOME_DAY, which is parametrized by the day on which 
the deliberation on whether it is possible to have a hanging after this day that will be a surprise 
to the person being executed. This definition appears to be the one the executioners use 
to determine whether it is ok to hang someone on a given day. 

To determine this, each day they ask :
Will this evil fellow be able to know for sure/predict that we will be hanging him on the day we plan 
to hang him?! 

If he is not able to predict his hanging right up until the day before, they can 
hang him the next morning and go to bed and night with the clear conscience of having surprised a 
dead guy.

This is the reasoning that executioners appear to follow in the paradox, which allows them 
to hang the person on Wednesday without introducing any contradictions into the system.

Note that this definition has the flavour of temporal logic. In particular, we are reasoning about 
a collection of judgemets (propositions) parametrized by the day on which they are being reasoned about.
Each day has a distinct proposition associated with it. This is
similar to how the context in temporal logic contains a structure,
together with a position in time. 

In Coq, we are already operating 
in the logic with enough expressivity to model temporal logic within it. One example of such an implementation 
of temporal logic in Coq can be found here :
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.30.3050&rep=rep1&type=pdf

We chose not to introduce the full machinery of temporal logic in this case, as we did not 
need most of it to describe the problem being studied here, nor did it promise to improve the ease of reasoning.

The other type of logic commonly seen in formalizations of the paradox is modal logic. 

Build this as state machine contract and run on Cardano.

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

(* td is on or after the day d *)
Definition isOnOrAfter td d := ~(isBefore td d).

(* wd1 is before wd2 *)
Fixpoint isBefore_WAB wd1 wd2 :=
match wd2 with
  | dayBefore => False
  | someWeekDay d => isBefore wd1 d
end.

(* NOTE : Axioms are everything the person getting hanged KNOWS FOR SURE *)
(* They are propositions that are true about the system independently of 
   the executioners' decision on when exactly to hang the person *)

(* the axiom stating hanging definitely happens on one of the weekdays *)
Axiom hanging_definitely_happens : hangingHappens.

(* if the hanging happens on day d, it does not happen on any other day *)
Axiom only_one_hanging : forall d : weekDay, (hangingOnDay d) -> (forall d' : weekDay, (hangingOnDay d') -> (d = d')).

(* NOTE : we cannot add a general axiom stating that we know the past, because we can only use knowledge of the 
   past when proving a proposition where the "today" is fixed, and the proposition says something 
   about the unexpected hanging in the context of knowledge available on a specific day *)

(* proving that a hanging happened today or before lets us arrovie at a contradiction *)
Definition noHangingYet (td : weekAndBefore) := forall d, (isOnOrAfter td d) -> (~ hangingOnDay d).

(* eq on days is decidable *)
Definition dayEqDec : forall x d : weekDay, (x=d \/ x<>d). 
Proof.
  destruct d, x; intuition discriminate.
Qed.

(* Definition of surprised assumed by the person being hanged 
   No matter what day the surprise actually happens, the 
   person expects to be surprised by it on every day of the 
   week leading up to the day of the hanging

   Ei. It is only ever possible to specify when the hanging happened 
   after it happened.

   This definition of surprise is not parametrized by what today 
   td is because it is independent of it --- it describes formally 
   the concept of prediction. We cannot know when a hanging occurst 
   unless it occured already *)
Definition SURPRISED_ALWAYS := forall td d, 
  hangingOnDay d -> isOnOrAfter td d.

(* NOTE : Use of negation in (~ hangingOnDay d) :
   Because we are using constructive logic, negating (hangingOnDay d) does not 
   necessarily mean that hanging did not happen on that day, and we can prove that.
   We may not have enough information to conclude this. Instead, (~ hangingOnDay d)
   means that "proving that hanging happend on the given day d also 
   proves False, and therefore, a proof of hanging on day d introduces an inconsistency
   to the system" *)

(* A weaker version of the surprise definition, which might?? have the same implication about 
   the impossibility of surprise 

   This one says that if we specify a hanging day that is before today, we get a 
   contradiction. Or, as explained above in the negation note, 
   for a day after today, we cannot prove the hanging happened. *)
Definition SURP_WEAK := forall td d, 
  isBefore td d -> ~hangingOnDay d.

(* SURPRISED_ALWAYS implies the weaker surprise definition *)
Lemma same_surp : SURPRISED_ALWAYS -> SURP_WEAK.
Proof.
  unfold SURPRISED_ALWAYS. unfold SURP_WEAK. 
  unfold isOnOrAfter. intros supDef td d. generalize (supDef td d).
  assert (~~isBefore td d <-> isBefore td d). compute. 
  destruct d; destruct td; try tauto; destruct w; try tauto.
  tauto.
Qed.

(* On a specific day td, a person can be surprised by a future hanging whenever :
   The hanging has not happened yet 
   AND 
   predicting a hanging on any future day leads to a contradiction. *)

(* for each day td, *)
Definition SURPRISED_SOME_DAY (td : weekAndBefore) :=  
  (* the hanging did not yet happen up to the day td *)
  (forall d_past, (isOnOrAfter td d_past) -> (~ hangingOnDay d_past))
  /\
  (* for any day d in the future (ie. day d after today),
  proving that hanging happens on the day d leads to a contradiction *)
  (forall d, isBefore td d -> ~hangingOnDay d).
 

(* If being surprised by a hanging is possible, today's day td
   must be before thrusday *)
Lemma surprised_not_friday (td : weekAndBefore) : SURPRISED_SOME_DAY td -> isBefore td thursday.
Proof.
  generalize only_one_hanging; generalize hanging_definitely_happens; 
  unfold SURPRISED_SOME_DAY; intros hangHappens onlyOne surpDay.
  destruct surpDay as [pastNo noFuture].
  compute in hangHappens; unfold isOnOrAfter in pastNo.
  destruct td; try (destruct w); compute; try tauto;
  apply hangHappens; intros d hD; apply (noFuture d); 
  generalize (pastNo d); destruct d;
  compute; try tauto.
Qed.



(* This part shows the reasoning of the person being hanged which 
   leads them to conclude, starting from the definition of surprise 
   as in SURPRISED_ALWAYS, that the hanging cannot happen any day *)

(* SURPRISE implies that hanging can't be on friday *)
Lemma noFri : SURPRISED_ALWAYS -> ~ hangingOnDay friday. 
Proof.
  generalize hanging_definitely_happens.
  compute. intros. elim H. intros.
  assert (d=friday). 
  generalize (only_one_hanging d H2 friday). compute. intros.
  generalize (dayEqDec d friday). intros.
  inversion H4. auto. tauto.
  generalize (H0 (someWeekDay thursday) friday H1). tauto. 
Qed.

(* SURPRISE implies that hanging can't be on thursday *)
Lemma noThurs : SURPRISED_ALWAYS -> ~ hangingOnDay thursday. 
Proof.
  unfold SURPRISED_ALWAYS.
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
Lemma noWed : SURPRISED_ALWAYS -> ~ hangingOnDay wednesday. 
Proof.
  unfold SURPRISED_ALWAYS.
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
Lemma noTue : SURPRISED_ALWAYS -> ~ hangingOnDay tuesday. 
Proof.
  unfold SURPRISED_ALWAYS.
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
Lemma noMon : SURPRISED_ALWAYS -> ~ hangingOnDay monday. 
Proof.
  unfold SURPRISED_ALWAYS.
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
Theorem surpriseIsWrong : ~SURPRISED_ALWAYS.
Proof.
  intro S.
  generalize (noFri S). generalize (noThurs S). generalize (noWed S). generalize (noTue S). generalize (noMon S).
  generalize hanging_definitely_happens. 
  unfold hangingHappens. intros. elim H. intro x. destruct x; tauto.
Qed.

(* if a hanging is on day d, and today is before that day, then no hanging happened yet *)
Lemma notBefore : forall td, forall d, hangingOnDay d -> isBefore td d -> noHangingYet td.
Proof.
  intros.
  destruct td.
  compute. tauto.
  unfold noHangingYet. intros. intro.
  generalize (only_one_hanging d H d0). intros.
  generalize (dayEqDec d d0). intros.
  inversion H4. 
  apply H1. rewrite <- H5. tauto. tauto.
Qed.



