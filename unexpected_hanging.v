(* The definition of a paradox is : "A paradox is a logically self-contradictory statement or a statement 
that runs contrary to one's expectation."

This conflates two very different things. The unexpected hanging paradox can be interpreted as 
either of those. Most of all, however, this paradox arises from lack of consensus between parties on 
the definitions of the terms and concepts used to make conclusions. 

Cite modal logic efforts!
Interpretation #1 - False proves anything, including any hanging day (both self-contradictory 
but also gives conclusions contrary to expectations)
#2 - The guards and person being hanged had distinct interpretations of surprise
*)

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

The system which we are about to describe is a formal representation of the knowledge
the prisoner has about the execution. 
We assume prisoner has accurate knowledge of the system and guards (or anyone else) do not 
have the agency to change the system. We assume guards have a day planned for the execution 
in advance, and the prisoner is not able to obtain knowledge about which day it is. 
We limit our meta-reasoning here to being 
strictly about the definition of surprise, rather than about any changes to other constraints 
of the system, or guards' plans. 

Sidenote : we could have separate modules representing two different scopes of 
knowledge : that of the prisoner (and, probably, of any spectators), and that of the executioners. 
We implicitly only have one knowledge scope here, since the executioners' knowledge scope is 
not interesting. It contains the exact day on which the hanging happens. 
We could even define a relationship between those scopes of 
knowledge, but it can generally be summed up by "the executioners do not tell the prisoner 
when the hanging will happen". 

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

This definition seems to have the flavour of temporal or perhaps modal logic. In particular, we are reasoning about 
a collection of judgemets (propositions) parametrized by the day on which they are being reasoned about, like one would 
using temporal logic.
We are also reasoning about an event that may happen on some days, and will definitely happen on one of the 
days, which looks like modal logic.
In Coq, we are already operating 
in the logic with enough expressivity to model temporal logic within it. One example of such an implementation 
of temporal logic in Coq can be found here :
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.30.3050&rep=rep1&type=pdf

The case we are reasoning about, however, is not describable by modal or temporal logic. 
It is not simply the conclusions (provable propositions) which we can derive using the rules of the 
logic + the axioms of the 
It is not the provability of the proposition about whether the definition of surprise, or the conditions under which it holds, that 
system that change based on the day. It is the actual specification of the proposition about which 
we reason (ie. the definition of surprise itself) that changes for each day of the week, not just 
Each day has a distinct proposition associated with it. This is
similar to how the context in temporal logic contains a structure,
together with a position in time. 

Not a common definition of surprise, but a distinct one for each day. We must say something about how to 
collate them together without contradiction. The surprise requirement by the guards is formulated as an
exclusion of those day's surprise definitions that lead to contradiction. ~~ SURPRISE must then hold true
with those excluded.


Build this as state machine contract and run on Cardano.

*) 

(* week days *)
Inductive weekDay : Type :=
  | monday : weekDay
  | tuesday : weekDay
  | wednesday : weekDay
  | thursday : weekDay
  | friday : weekDay.

Inductive weekDayAfterMon : Type :=
  | tuesdayM : weekDayAfterMon
  | wednesdayM : weekDayAfterMon
  | thursdayM : weekDayAfterMon
  | fridayM : weekDayAfterMon.

Inductive weekDayAfterTue : Type :=
  | wednesdayTu : weekDayAfterTue
  | thursdayTu : weekDayAfterTue
  | fridayTu : weekDayAfterTue.

Inductive weekDayAfterWed : Type :=
  | thursdayW : weekDayAfterWed
  | fridayW : weekDayAfterWed.

Inductive weekDayAfterThurs : Type :=
  | fridayTh : weekDayAfterThurs.

(*
Definition sdkf (A B : Prop) : ((A \/ ~A) /\ (A -> B)) -> B \/ ~B.
intros. tauto. *)

(* a week day OR some day before the week starts,
the type used to specify a "today" *)
Inductive weekAndBefore : Type :=
  | dayBefore : weekAndBefore
  | someWeekDay : weekDay -> weekAndBefore.

(* hangingOnDay (d) means that hanging happened on day d *)
(* it means we know and can prove it happened on day d *)
Variable hangingOnDay : weekDay -> Prop.

(* the proposition stating that it's not true that hanging happens on 
none of the weekdays 

This is a wrong definition i think 
Definition hangingHappens := ~(forall d, ~hangingOnDay d). *)

(* Because equality and <=/>= relations are decidable, we cannot use them in constructive 
predicates involving implications of the form A -> B, as that *)






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

(* td is on or after td_after *)
Definition isOnOrAfter_WAB td_after td := ~(isBefore_WAB td_after td).

(* eq on days is decidable *)
Definition dayEqDec : forall x d : weekDay, (x=d \/ x<>d). 
Proof.
  destruct d, x; intuition discriminate.
Qed.

(* if the hanging happens on day d, it does not happen on any other day *)
Definition only_one_hanging_prop := forall d d' : weekDay, (hangingOnDay d /\ hangingOnDay d') -> d = d'.

(* if the hanging happens on day d, it does not happen on any other day *)
Definition only_one_hanging_IF_HAPPENED := (exists d, (hangingOnDay d)) -> forall d d', (hangingOnDay d) -> (forall d' : weekDay, (hangingOnDay d') -> (d = d')).

(* this predicate is provable if for days up to and including today, we can prove whether the 
hanging did or did not occur *)
Definition knowPast (td : weekAndBefore) := forall d, isOnOrAfter td d -> hangingOnDay d \/ ~ hangingOnDay d.

(* no hanging has occured up to today if we can prove that there is no day on or before today
such that a hanging is provable that day *)
Definition noHangingYet (td : weekAndBefore) := forall d, isOnOrAfter td d -> ~ hangingOnDay d.

(* both directions is wrong *)
Definition hangingHappens := ~(forall d, ~hangingOnDay d).

Definition unexp_hanging_preconditions := hangingHappens /\ only_one_hanging_prop.

Definition RelationalChoice_one :=
    (exists y : weekDay, hangingOnDay y) ->
    (exists R' : weekDay->Prop, (forall y, R' y -> hangingOnDay y) /\ exists! y, R' y).

Lemma rew (A B : Prop) : (A /\ ~B) -> ~(A -> B).
tauto.
Qed.

  Definition exists_unique_happens :=
    exists d, ((~~ hangingOnDay d)
    /\
      (forall d',
      ~~ hangingOnDay d
      -> ~~ hangingOnDay d'
      -> d = d') ->
      (hangingOnDay d)).

Lemma euh_imp_classical :
    exists_unique_happens /\ only_one_hanging_prop ->
    (forall d,
    ~ hangingOnDay d \/ hangingOnDay d).
compute. intros. destruct H. destruct H.
generalize (dayEqDec x d). intro.
inversion H1. right. 
rewrite H2 in H. apply H. split.

 left.  rewrite <- H1. intro. 

apply H.
a


  Lemma cantBeSurpFriday :
    twoPossible_PRDX (someWeekDay thursday)
    $\to$ False.

Lemma nRC :( ~ RelationalChoice_one) -> False. (*~ only_one_hanging_prop.*)
compute. intros.
apply H. intros. destruct H0. 
exists (fun d' =>  x = d').
split. intros. rewrite <- H1. auto.
exists x. auto. generalize (H2 y). intro.  destruct H3. auto.
exists x. split. intros. split. exact (H0 x).
intros. symmetry. apply (H2 x).

Check (H0 x).
assert (t : exists y : weekDay, hangingOnDay y).
exists d. auto. generalize (H0 t). intro.
destruct H3. destruct H3. generalize (H3 d). generalize (H3 d').
intros. replace (d=d') with (~d<>d'). intro.


Lemma nRC : ~only_one_hanging_prop -> ~RelationalChoice_one.
compute. intros.
apply H. intros. destruct H1.
assert (t : exists y : weekDay, hangingOnDay y).
exists d. auto. generalize (H0 t). intro.
destruct H3. destruct H3. generalize (H3 d). generalize (H3 d').
intros. replace (d=d') with (~d<>d'). intro.

 destruct H4.
destruct H4. apply (H5 


assert (notB : ~(exists R' : weekDay -> Prop,
      (forall y : weekDay, R' y -> hangingOnDay y) /\
      (exists x : weekDay,
         R' x /\
         (forall x' : weekDay, R' x' -> x = x')))).
intro. destruct H0. destruct H0. destruct H1.
destruct H1. 


assert (H2r : forall x' : weekDay, x x' -> x0 <> x' -> False).
intros. apply H4. apply H2. auto. apply H2r.

Definition RelationalChoice_one :=
    (exists y : weekDay, hangingOnDay y) ->
    (exists R' : weekDay->Prop, subrelation R' hangingOnDay /\ exists! y, R' y).



Definition choice :=
   (P : weekDay -> Prop),  
   (exists b : B, P b) ->
   exists fb : B, P fb.

Definition RelationalChoice_on :=
  forall R:A->B->Prop,
    (forall x : A, exists y : B, R x y) ->
    (exists R' : A->B->Prop, subrelation R' R /\ forall x, exists! y, R' x y).



(* axiom of choice in disguise! *)
Definition A (T : Type) : Set := { T }.
B = weekDay 
P _ d = forall d' : weekDay, hangingOnDay d /\ hangingOnDay d' -> d = d'
Definition choice :=
   forall (A B : Type) (P : A -> B -> Prop),  
   (forall a : A, exists b : B, P a b) ->
   exists f : A -> B, forall a : A, P a (f a).

exists pickHangingDay : { weekDay } -> weekDay
forall (w : { weekDay }), P w (pickHangingDay w)

forall pickHangingDay : { weekDay } -> weekDay
exists (w : { weekDay }), ~ P w (pickHangingDay w)



Definition uh_imp_classical : hangingHappens /\ only_one_hanging_prop -> forall d, hangingOnDay d \/ ~hangingOnDay d.
intros. destruct H. unfold hangingHappens in H. unfold only_one_hanging_prop in H0.
generalize (dayEqDec d). intro.
right. intro. apply H. intros. intro.
generalize (H0 d). destruct d.

Definition cantBeSurprised := forall d, hangingOnDay d \/ ~ hangingOnDay d.

Definition canBeSurprisedByFutureHang (td : weekAndBefore) := 
  exists (d d' : weekDay), d <> d' /\ ~~hangingOnDay d /\ ~~hangingOnDay d' /\ isBefore td d /\ isBefore td d'.

Variable P : nat -> Prop.

Definition myfunc (td : weekAndBefore) := 
  exists (d d' : nat), d <> d' /\ ~~P d /\ ~~P d'/\ d < d'.

Variable td : weekAndBefore.

Definition ACclass : only_one_hanging_prop -> forall d, hangingOnDay d \/ ~ hangingOnDay d.
intros. 
generalize (H d ).
generalize dayEqDec. intros.
Admitted.

Definition onePossible (td : weekAndBefore)  := ((isBefore td friday /\ noHangingYet td) -> exists d, isBefore td d /\ ~~hangingOnDay d) 
/\ (td = someWeekDay friday -> exists d, hangingOnDay d) -> hangingOnDay friday.

only_one_hanging_prop

Definition oneInsNotEnough : onePossible (someWeekDay thursday) -> False.
compute. intros. destruct H. destruct H.

Definition onePossibleAll := forall td, noHangingYet td -> exists d, isBefore td d /\ ~~hangingOnDay d) 
/\ (td = someWeekDay friday -> exists d, hangingOnDay d) -> hangingOnDay friday.

Fixpoint canBeSurprisedByFutureHangFix (d0 : weekDay) : Prop :=
  exists (d d' : weekDay), d <> d' /\ ~~canBeSurprisedByFutureHangFix d 
    /\ ~~canBeSurprisedByFutureHangFix d' /\ isBefore td d /\ isBefore td d'.

a friday hanging is only not a surprise (provable) if you already know that a hanging did not occur mon-thurs
but you cannot know/prove that until you get to thursday

getHangingProp d hangingOnDay

hanging

getExpOnD f (d : weekDay)

Furthermore, if p is a primitive proposition
such that all free3
 occurrences of p in phi are positive and there is no
free occurrence of p in a subformula of phi of the form fix q.psy, then
fix p.phi (read "fix of phi (with respect to p)") is a formula. 


axiom of choice in disguise!
A = { weekDay }
B = weekDay 
P _ d = forall d' : weekDay, hangingOnDay d /\ hangingOnDay d' -> d = d'
Definition choice :=
   forall (A B : Type) (P : A -> B -> Prop),  
   (forall a : A, exists b : B, P a b) ->
   exists f : A -> B, forall a : A, P a (f a).

exists pickHangingDay : { weekDay } -> weekDay
forall (w : { weekDay }), P w (pickHangingDay w)

forall pickHangingDay : { weekDay } -> weekDay
exists (w : { weekDay }), ~ P w (pickHangingDay w)



choice weekDay _ (fun d 


F f n = (isZero n) 1 (multiply n (f (pred n)))

F (canBeSurprisedByFutureHangFix td) d = 
     exists (d d' : weekDay), d <> d' /\ ~~canBeSurprisedByFutureHangFix td d 
       /\ ~~canBeSurprisedByFutureHangFix td d' /\ isBefore td d /\ isBefore td d'.


Definition canNotBeSurprisedByFutureHang (td : weekAndBefore) := 
  exists d, hangingOnDay d /\ isBefore td d.

(* on Sunday, when isBefore and noHangingYet is trivially true, 
we cannot prove the following for arbitrary (including non-classical) predicate hangingOnDay 
Therefore we cannot prove that the hanging happens on a specific day when today is sunday *)
Definition surpriseDoesntImplySure := canBeSurprisedByFutureHang dayBefore -> 
  exists d, hangingOnDay d.

(* it is not possible to disprove a hanging doesnt happen any day if surprise is possible on sunday *)
Lemma surpriseImpHangingHappens : canBeSurprisedByFutureHang dayBefore -> 
  ~(forall d, ~hangingOnDay d).
Proof.
  intros cbs. intro. destruct cbs as [d nd].
  destruct nd as [d' cd]. destruct cd  as [ne  r]. destruct r as [nnd r].
  destruct r as [nnd' r]. destruct r as [ibd ibd'].  apply nnd.
  intro. exact (H d H0).
Qed.


Lemma cantBeSurpFriday : (noHangingYet (someWeekDay thursday) /\ canBeSurprisedByFutureHang (someWeekDay thursday)) -> False.
Proof.
  intros. destruct H as [ nhy cbs]. destruct cbs as [d nd].
  destruct nd as [d' cd]. destruct cd  as [ne  r]. destruct r as [nnd r].
  destruct r as [nnd' r]. destruct r as [ibd ibd']. 
  assert (df : d = friday). destruct d; compute in ibd; tauto.
  assert (df' : d' = friday). destruct d'; compute in ibd'; tauto.
  rewrite df in ne. rewrite df' in ne. apply ne. reflexivity.
Qed.

(* is statement below true for all hangingOnDay ? *)
Lemma surpriseDoesntImplySure : forall td, (isBefore td thursday /\ noHangingYet td /\ canBeSurprisedByFutureHang td -> exists d, hangingOnDay d) -> False.
intros. destruct H as [ib nhy]. appl
assert (ns : ~(exists d : weekDay, hangingOnDay d) -> ~canBeSurprisedByFutureHang td). tauto.
apply ns. ->
     

Lemma canBeSurpBeforeThurs (td : weekAndBefore) : unexp_hanging_preconditions /\ noHangingYet td 
  /\ isBefore td thursday -> canBeSurprisedByFutureHang td.
Proof.
  intros. destruct H as [hp nhy]. destruct hp as [hh ooh].
  destruct nhy as [nhy isb]. 
  unfold canBeSurprisedByFutureHang. exists thursday. exists friday.
  split. compute. intro h. inversion h. split.
  generalize (nhy thursday). unfold isOnOrAfter. tauto. split.
  assert (isBefore td friday). destruct td; try (destruct w); try tauto. compute. auto. 
  generalize (nhy friday). unfold isOnOrAfter. tauto. split. auto.
  destruct td; try (destruct w); try tauto. compute. auto. 
Qed.

Lemma cantHaveTwoMaybes : (only_one_hanging_prop /\ (exists (d d' : weekDay), d <> d' /\ ~~hangingOnDay d /\ ~~hangingOnDay d')) -> False.
Proof.
  intro hyp. destruct hyp as [ooh nt]. destruct nt. destruct H. destruct H.
  unfold only_one_hanging_prop in ooh. generalize (ooh x). intro. apply H. 
  assert (kj  : forall d' : weekDay, hangingOnDay d' -> hangingOnDay x -> x = d').
  intros. exact (H1 H3 d' H2). generalize (kj x0). tauto.
Qed.

Lemma skdjf (A B : Prop) : ~(A /\ B) -> ((A -> ~B) /\ (B -> ~A)).
tauto.
Qed.

Lemma 

Lemma bad (td : weekAndBefore) : unexp_hanging_preconditions /\ noHangingYet td 
  /\ isBefore td thursday -> False.
unfold unexp_hanging_preconditions. unfold noHangingYet. 
intros. destruct H as [hp nhy]. destruct hp as [hh ooh].
apply hh. intros. intro. destruct nhy as [ny ib]. destruct (ny d) as [ioh hio].
clear hh. generalize (ooh d H). intro.
assert (bd : forall d' : weekDay, ~~hangingOnDay d' -> d = d' ).
intros. assert (te : ~~d = d' -> d = d'). Focus 2. apply te. intro.
generalize (H0 d'). tauto. Focus 2.
assert (bdd : d = thursday \/ d = friday). Focus 2.
elim bdd. intro. rewrite H1 in bd. generalize (bd friday). intro. 
assert (~thursday = friday). intro. inversion H3.
rewrite H1 in ioh. rewrite H1 in hio. 
unfold isOnOrAfter in ioh. unfold isOnOrAfter in hio.
unfold isOnOrAfter in ny. generalize (ny friday). 
assert (isBefore td friday). Focus 2. tauto.
destruct td; try destruct w;try tauto. intro.
elim bdd. intro. rewrite H1 in H2. inversion H2. tauto. generalize (bd thursday). intro. 
assert (~friday = thursday). intro. inversion H4.
rewrite H1 in ioh. rewrite H1 in hio. 
unfold isOnOrAfter in ioh. unfold isOnOrAfter in hio.
unfold isOnOrAfter in ny. generalize (ny friday). 
assert (isBefore td friday). Focus 2. tauto.
destruct td; try destruct w;try tauto.

 tauto. inversion H2.

apply ioh. intro.  rewrite H1 in ioh. compute in ioh.
apply bd.
introd <>.

having two possible days where we cant disprove the hanging contradicts having a unique hanging day
even in constructive logic
If we eliminated at least 4 days, we have proven false. 
positive vs negative occurence, lets us prove contradiction from ~~h instead of h.
two possible hangings on any two different days is false iff two definite hangings on different days is false 
because day equality is classical

if we drop the "exactly one hanging" constraint, and instead consider when the first hanging happens 
as what we want to be surprised by, the semantics of the problem (ie. if we prove a hanging 
happens on a specific day, we have proved false) remains the same.

(hangingOnDay d /\ hangingOnDay d') is already false whether or not d = d', since surprise 
means we should not be able to prove that hanging is on a specific day, so we have False -> d=d'
having a unique hanging day means we can prove hanging happened on a specific day, not just 
that it maybe happened.

the only thing we can know about the future is that there must be at least two distinct days for which 
we are not able to disprove that the hanging happens. we know everything about the past (ie 
no hanging occured yet). try proving - "(surprise implies that there are two days in which 
hanging happens) is false". if each day we know all days up to today, by thursday there will not be 
two days distinct for which the hanging is possible. two distinct possible days contradicts 
uniqueness of hanging

We do not lose anything by dropping the idea that we care about the unique day in which the 
hanging happens, and instead should care about the first occurence of it. Semantically this 
solves the same problem, because we only care about what we know before the hanging happens.
Hanging being a surprise is the lack of certainty about when it will happen in the future. 
Once it happens, there is no more surprise. So, the first occurence of the hanging breaks 
the surprise conditions required to be satisfied to remain within the constraints of the problem, 
and therefore whether or not another hanging happens after the first one is outside 
the scope of the situation being reasoned about.

can be surprised by *A* hanging in the future. For each day today td, 
"(1) can be surprised and no hanging yet" 
preconditions, "(2) can NOT be surprised and no hanging yet", and "(3) hanging already happened" 
preconditions are mutually exclusive!
We can add that supposing the hanging already happened on some day takes us outside of 
the surprise constraints. Saying that additional 
hanging will occur  would be surperfluous to specifying the problem, since we care 
to explore when surprise is possible, and we already know its not possible once hanging happened.

at the time when the prohibition of (additional) hangings is enacted, no-hanging + surprise no longer holds.


Lemma noSurpriseFriday : unexp_hanging_preconditions /\ noHangingYet (someWeekDay thursday) 
  -> canNotBeSurprisedByFutureHang (someWeekDay thursday).
Proof.
  compute. intros. destruct H as [hp nhy]. destruct hp as [hh ooh].
  exists friday. split; auto. 
  assert (nhm : hangingOnDay monday -> False). intro nh.
  generalize (nhy monday). intros. tauto. 
  assert (nht : hangingOnDay tuesday -> False). intro nh.
  generalize (nhy tuesday). intro. inversion H0.
  assert (nhw : hangingOnDay wednesday -> False). intro nh.
  generalize (nhy wednesday). intro. inversion H0.
  assert (nhth : hangingOnDay thursday -> False). intro nh.
  generalize (nhy thursday). intro. inversion H0.

generalize (nhy  apply hh. destruct H2. auto. 
Qed.

notNoSurpMeansCanBeSurp : forall td, cantBeSurprised -> ~canBeSurprisedByFutureHang

Lemma nnOoh : only_one_hanging_prop -> forall d : weekDay, (~hangingOnDay d) -> (forall d' : weekDay, (~hangingOnDay d') -> (d = d')).
intros. unfold only_one_hanging_prop in H. replace (d = d') with (~ d <> d'). 
intro. generalize (H d); intro. 
assert (vvv : (forall d' : weekDay, hangingOnDay d' -> d = d') \/ (~ hangingOnDay d)). tauto. tauto.
apply H0. apply

Definition dontKnowFuture (td : weekAndBefore) :=
  forall d, hangingOnDay d -> isOnOrAfter td d.

Definition canBeSurprised (td : weekAndBefore) := 
  noHangingYet td /\ dontKnowFuture td /\ exists d, isBefore td d.

Definition canBeSurprisedAlways := forall td, canBeSurprised td.

Lemma noSurpriseFriday : unexp_hanging_preconditions -> ~canBeSurprised (someWeekDay friday).
Proof.
  compute. intros. destruct H0. destruct H1. destruct H2. auto. 
Qed.

Lemma noSurpriseThursday : unexp_hanging_preconditions -> ~canBeSurprised (someWeekDay thursday).
Proof.
  compute. intros hangp cbs. destruct cbs as [nhy dkfexd]. destruct dkfexd as [dkf exd]. elim (dkf friday); auto.
  destruct hangp as [hh ooh]. intro. 
  assert (nhm : hangingOnDay monday -> False). intro nh.
  generalize (ooh monday nh friday H). intro. inversion H0.
  assert (nht : hangingOnDay tuesday -> False). intro nh.
  generalize (ooh tuesday nh friday H). intro. inversion H0.
  assert (nhw : hangingOnDay wednesday -> False). intro nh.
  generalize (ooh wednesday nh friday H). intro. inversion H0.
  assert (nhth : hangingOnDay thursday -> False). intro nh.
  generalize (ooh thursday nh friday H). intro. inversion H0.

generalize (nhy monday).
  generalize (nhy tuesday). generalize (nhy wednesday). 
  generalize (nhy thursday). 
  destruct H. clear H2. apply (H1 friday); auto. right. intro. apply (H1 friday). tauto. tauto.  
Qed.





Lemma bad : unexp_hanging_preconditions -> ~dontKnowFuture dayBefore.
Proof.
  intros uh. destruct uh as [hh ooh]. unfold dontKnowFuture. 
  intro dnf. apply hh. intros. intro.
  unfold only_one_hanging_prop in ooh. destruct d. 
  unfold isOnOrAfter in dnf. apply (dnf monday). tauto. compute. auto.
  unfold isOnOrAfter in dnf. apply (dnf tuesday). tauto. compute. auto.
  unfold isOnOrAfter in dnf. apply (dnf wednesday). tauto. compute. auto.
  unfold isOnOrAfter in dnf. apply (dnf thursday). tauto. compute. auto.
  unfold isOnOrAfter in dnf. apply (dnf friday). tauto. compute. auto.
  destruct d.
  unfold isOnOrAfter in cbs. apply (cbs monday). tauto. compute. auto.
  destruct w; compute; try tauto. apply (ny monday). compute. auto. auto.
  apply (ny monday). compute. auto. auto.
apply (ny monday). compute. auto. auto.
apply (ny monday). compute. auto. auto.
apply (ny monday). compute. auto. auto.
apply (ny tuesday). compute. auto. auto. intro. destruct w.
  destruct H. destruct H0. apply H0. intro.
  apply H1. intro. apply H. apply (ooh x H2 x0 H3).

  unfold hangingHappens in hh. apply hh.
  

 td noHang. destruct td. compute. tauto.
  intros d isOn. right. intro. apply (noHang d isOn). tauto. 
Qed.

(* one can be surprised on day td when (1) a hanging did not yet occur, and 
(2) surprise is still possible *)
Definition surprisedAlways := forall td, 
  noHangingYet td -> canBeSurprised.

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


(* proposition says that given a "today", (1) you know whether or not the hanging happened today or on prior days,
(2) you can be surprised by the hanging *)

Definition CAN_BE_SURPRISED_BY_HANGING_WITH_PAST_KNOWLEDGE_UP_TO (td : weekAndBefore) :=
  (* proving that  *)
  (forall d_past, (isOnOrAfter td d_past) -> (~hangingOnDay d_past \/ hangingOnDay d_past))
  /\ CAN_BE_SURPRISED_BY_HANGING.

Definition CAN_BE_SURPRISED_BY_HANGING_PARAM (h : weekDay -> Prop) :=
  forall d, ~~h d.

Definition CAN_BE_SURPRISED_BY_HANGING_WITH_PAST_KNOWLEDGE_UP_TO_PARAM (h : weekDay -> Prop) (td : weekAndBefore) :=
  (forall d_past, (isOnOrAfter td d_past) -> (~h d_past \/ h d_past))
  /\ CAN_BE_SURPRISED_BY_HANGING_PARAM h.

Definition hangingHappens_param (h : weekDay -> Prop) := ~(forall d, ~h d).

Definition only_one_hanging_param (h : weekDay -> Prop) := forall d : weekDay, (h d) -> (forall d' : weekDay, (h d') -> (d = d')).

Definition unexp_hanging_param (h : weekDay -> Prop) := hangingHappens_param h /\ only_one_hanging_param h.


Inductive hang : weekDay -> Prop :=
  | hang_mon : hang monday
  | hang_tue : hang tuesday
  | hang_wed : hang wednesday
  | hang_thur : hang thursday
  | hang_fri : hang friday.

Definition surp_today (td : weekAndBefore)  := CAN_BE_SURPRISED_BY_HANGING_WITH_PAST_KNOWLEDGE_UP_TO_PARAM hang td.

Definition unexp_hanging := unexp_hanging_param hang.

(*
  | even_S : forall n, odd n -> even (S n)
  with odd : nat -> Prop :=
  | odd_S : forall n, even n -> odd (S n).

Inductive hang : Prop :=
  | doHang : weekDay -> hang
  | preconditions : hang -> hang
  | can_surprise : hang -> weekAndBefore -> hang. 
Fixpoint interpretHang hangP td :=
match hang with
  | doHang =>
  | preconditions h => 

Fixpoint isBefore_WAB wd1 wd2 :=
match wd2 with
  | dayBefore => False
  | someWeekDay d => isBefore wd1 d
end.
forall (td : weekAndBefore),
*)


Lemma surprised_not_friday (td : weekAndBefore) 
  :  surp_today td /\ unexp_hanging -> isBefore td thursday.
Proof.
  intro su. destruct su as [st uh].
  destruct uh as [hh ooh].
  unfold hangingHappens_param in hh.
  unfold only_one_hanging_param in ooh.
  unfold surp_today in st.
  unfold CAN_BE_SURPRISED_BY_HANGING_WITH_PAST_KNOWLEDGE_UP_TO_PARAM in st. 
  destruct st as [knowPast noHang]. destruct td. compute. auto.
  destruct w; compute; try tauto. apply hh; intros; intro.
  destruct (knowPast thursday). compute. auto. apply (noHang thursday). auto.
  apply (noHang wednesday). intro. generalize (ooh wednesday H1 thursday H0). 
  intro wt. inversion wt.
  compute in knowPast. apply hh. intros. intro. generalize (knowPast d). generalize (noHang d).
  intros. assert (t : False -> False). auto. generalize (H1 t). intro.
  inversion H2. tauto. 
  assert (dh : exists d', d' <> d). destruct d. exists friday. 
  intro ne. inversion ne. exists monday. intro ne. inversion ne. 
  exists tuesday. intro ne. inversion ne. exists wednesday. intro ne. inversion ne.
  exists thursday. intro ne. inversion ne. destruct dh as [d' ne].
  assert (nd' : ~ hang d'). intro. apply ne. apply ooh; auto. 
  apply (noHang d'). auto.
Qed.

Lemma prop_exists : exists (h : weekDay -> Prop), hangingHappens_param h.
exists hang. compute. intros.


Lemma surprised_sunday  
  :  ~~ (unexp_hanging /\ surp_today dayBefore) .
Proof.
  compute. intro. apply H. split. split. intro. assert ( apply H0. 
Admitted.

(* if you are surprised by hanging, today has to be mon, tue, or wed
we dont yet say anything here about whether or not being surprised on thursday or friday is possible *)

Lemma surprised_not_friday (hanging : unexp_hanging_preconditions) (td : weekAndBefore) 
  :  CAN_BE_SURPRISED_BY_HANGING_WITH_PAST_KNOWLEDGE_UP_TO td -> isBefore td thursday.
Proof.
  destruct hanging as [hh ooh].
  unfold hangingHappens in hh.
  unfold only_one_hanging_prop in ooh.
  unfold CAN_BE_SURPRISED_BY_HANGING_WITH_PAST_KNOWLEDGE_UP_TO.
  unfold CAN_BE_SURPRISED_BY_HANGING. 
  intro surpDay. destruct surpDay as [knowPast noHang]. destruct td. compute. auto.
  destruct w; compute; try tauto. apply hh; intros; intro.
  destruct (knowPast thursday). compute. auto. apply (noHang thursday). auto.
  apply (noHang wednesday). intro. generalize (ooh wednesday H1 thursday H0). 
  intro wt. inversion wt.
  compute in knowPast. apply hh. intros. intro. generalize (knowPast d). generalize (noHang d).
  intros. assert (t : False -> False). auto. generalize (H1 t). intro.
  inversion H2. tauto. 
  assert (dh : exists d', d' <> d). destruct d. exists friday. 
  intro ne. inversion ne. exists monday. intro ne. inversion ne. 
  exists tuesday. intro ne. inversion ne. exists wednesday. intro ne. inversion ne.
  exists thursday. intro ne. inversion ne. destruct dh as [d' ne].
  assert (nd' : ~ hangingOnDay d'). intro. apply ne. apply ooh; auto.
  apply (noHang d'). auto.
Qed.

(* you cannot disprove that before thursday, it is possible to be surprised by a hanging *)

Lemma surprised_sunday  
  :  ~~ (unexp_hanging_preconditions /\ CAN_BE_SURPRISED_BY_HANGING_WITH_PAST_KNOWLEDGE_UP_TO dayBefore) .
Proof.
  compute. intro. apply H. split. 
Admitted.


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



