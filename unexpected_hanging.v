

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


(* eq on days is decidable *)
Definition dayEqDec : forall x d : weekDay, (x=d \/ x<>d). 
Proof.
  destruct d, x; intuition discriminate.
Qed.


Definition uniqueHanging
    (td : weekAndBefore) :=
  forall d d',
  isBefore td d /\ isBefore td d' ->
  hangingOnDay d ->
  hangingOnDay d' ->
  d = d'.

(* no hanging has occured up to today if we can prove that there is no day on or before today
such that a hanging is provable that day *)
Definition noHangingYet (td : weekAndBefore) := forall d, isOnOrAfter td d -> ~ hangingOnDay d.


Definition onePossiblePRDX (td : weekAndBefore)  :=
  (td = someWeekDay friday
    -> exists d, hangingOnDay d)
  /\
  ((exists d, hangingOnDay d)
    -> uniqueHanging dayBefore)
  /\
  ((isBefore td friday /\ noHangingYet td) ->
    exists d, isBefore td d /\ ~~ hangingOnDay d).


Definition existsUniqueHappens :=
  (exists d, ~~ hangingOnDay d)
  /\
  (forall d d',
    ~~ hangingOnDay d
    -> ~~ hangingOnDay d'
    -> d = d')
  ->
  exists d, hangingOnDay d.

Lemma euhImpClassical :
  (uniqueHanging dayBefore) ->
  (exists d, ~~ hangingOnDay d) ->
  existsUniqueHappens ->
  (forall d, ~ hangingOnDay d \/ hangingOnDay d).
Proof.
  compute. intros UH EP EUH d.
  destruct EP. generalize (dayEqDec d x).
  intro de. inversion de. rewrite <- H0 in H. 
  assert (EUHc : exists d : weekDay, hangingOnDay d).
  apply EUH. split. exists d. tauto.
  intros d0 d' nnd0 nnd'.
  assert (dd : (~ d0<> d') -> d0 = d').
  generalize (dayEqDec d0 d'). tauto.
  apply dd. intro d0d'.
  apply nnd0. intro hd0. apply nnd'. intro hd'.
  apply d0d'. apply (UH d0 d'). tauto. tauto. tauto.
  destruct EUHc. assert (x0 = d).
  assert (dd : (~ x0<> d) -> x0 = d).
  generalize (dayEqDec x0 d). tauto.
  apply dd. intro. 
  generalize (UH x0 d). tauto. rewrite H2 in H1.
  auto.

  left. intro. apply H. intro. generalize (UH d x). tauto. 
Qed.
 
Definition twoPossible
    (td : weekAndBefore) :=
  exists d d', d <> d'
  /\ ~~ hangingOnDay d
  /\ ~~ hangingOnDay d'
  /\ isBefore td d /\ isBefore td d'.

Definition twoPossiblePRDX
    (td : weekAndBefore)  :=
  (td = someWeekDay friday
    -> exists d, hangingOnDay d)
  /\
  ((exists d, hangingOnDay d)
    -> uniqueHanging dayBefore)
  /\
  ((isBefore td friday /\ noHangingYet td) ->
    twoPossible td).


Lemma cantBeSurpFriday :
  twoPossiblePRDX (someWeekDay thursday)
  -> noHangingYet (someWeekDay thursday)
  -> False.
Proof.
  unfold twoPossiblePRDX. intros. destruct H.
  compute in H1. compute in H0.
  destruct H1. 
  assert (H2pf : True /\
     (forall d : weekDay,
      (match d with
       | friday => True
       | _ => False
       end -> False) -> hangingOnDay d -> False) ). tauto.
  generalize (H2 H2pf). intro.
  destruct H3. destruct H3.
  destruct x; destruct x0; compute in H3; try tauto.
Qed.


Definition uniqueMaybe
    (td : weekAndBefore) :=
  forall d d',
  isBefore td d /\ isBefore td d' ->
  ~~ hangingOnDay d ->
  ~~ hangingOnDay d' ->
  d = d'.


Lemma uniqueMaybeEqv
    (td : weekAndBefore) :
  uniqueHanging td
  <->
  uniqueMaybe td.
Proof.
  split; unfold uniqueHanging; unfold uniqueMaybe; intros.
  assert (dd : (~ d<> d') -> d = d').
  generalize (dayEqDec d d'). tauto.
  apply dd. intro dd'. apply H1.
  intro. apply H2. intro. apply dd'.
  apply (H d d'); try tauto.
  generalize (H d d'). tauto.
Qed.
  

Lemma twoNotUnique :
  forall td,
  twoPossible td ->
  ~ uniqueHanging td.
Proof.
  unfold twoPossible; unfold uniqueHanging; intros.
  intro. destruct H. destruct H. destruct H.
  generalize (H0 x x0). tauto.
Qed.

(* test stuff *)


Definition uniqueHanging_param
    (hangingOn : weekDay -> Prop)
    (td : weekAndBefore) :=
  forall d d',
  isBefore td d /\ isBefore td d' ->
  hangingOn d ->
  hangingOn d' ->
  d = d'.

Definition noHangingYet_param
   (hangingOn : weekDay -> Prop)
   (td : weekAndBefore)
   := forall d, isOnOrAfter td d -> ~ hangingOn d.

Definition twoPossible_param
    (hangingOn : weekDay -> Prop)
    (td : weekAndBefore) :=
  exists d d', d <> d'
  /\ ~~ hangingOn d
  /\ ~~ hangingOn d'
  /\ isBefore td d /\ isBefore td d'.



Definition twoPossiblePRDX_param
    (hangingOn : weekDay -> Prop)
    (td : weekAndBefore) :=
  (td = someWeekDay friday
    -> exists d, hangingOn d)
  /\
  ((exists d, hangingOn d)
    -> uniqueHanging_param hangingOn dayBefore)
  /\
  ((isBefore td friday /\ noHangingYet_param hangingOn td) ->
    twoPossible_param hangingOn td).

Lemma existsHangFunc td :
  exists (hangingOn : weekDay -> Prop), 
  td <> (someWeekDay thursday) 
  -> twoPossiblePRDX_param hangingOn td.
Proof.
  destruct td.
  split; try split; destruct td; compute. split. split.


