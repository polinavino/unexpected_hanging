

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


(* no hanging has occured up to today if we can prove that there is no day on or before today
such that a hanging is provable that day *)
Definition noHangingYet (td : weekAndBefore) := forall d, isOnOrAfter td d -> ~ hangingOnDay d.

Definition uniqueHanging
    (td : weekAndBefore) :=
  forall d d',
  isBefore td d /\ isBefore td d' ->
  hangingOnDay d ->
  hangingOnDay d' ->
  d = d'.

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


Definition twoPossible
    (td : weekAndBefore) :=
  exists d d', d <> d'
  /\ ~~ hangingOnDay d
  /\ ~~ hangingOnDay d'
  /\ isBefore td d /\ isBefore td d'.


Lemma twoNotUnique :
  forall td,
  twoPossible td ->
  ~ uniqueHanging td.
Proof.
  unfold twoPossible; unfold uniqueHanging; intros.
  intro. destruct H. destruct H. destruct H.
  generalize (H0 x x0). tauto.
Qed.


Definition knowHanging (td : weekAndBefore) :=
(exists d, isOnOrAfter td d /\ hangingOnDay d) /\ (uniqueHanging dayBefore).

Definition dontKnowHanging (td : weekAndBefore) := ~ ((exists d, isBefore td d /\ hangingOnDay d)
/\ (uniqueHanging dayBefore)).

Definition surprise (td : weekAndBefore) := (noHangingYet td) /\ (twoPossible td).

Definition uniqueHanging_param
    (hangingOn : weekDay -> Prop)
    (hang : weekDay) (td : weekAndBefore) :=
  forall d d',
  isBefore td d /\ isBefore td d' ->
  hangingOn d ->
  hangingOn d' ->
  d = d'.

Definition noHangingYet_param
    (hangingOn : weekDay -> weekAndBefore -> weekDay -> Prop)
    (hang : weekDay) (td : weekAndBefore) :=
   forall d, isOnOrAfter td d -> ~ hangingOn hang td d.

Definition twoPossible_param
    (hangingOn : weekDay -> weekAndBefore -> weekDay -> Prop)
    (hang : weekDay) (td : weekAndBefore) :=
  exists d d', d <> d'
  /\ ~~ hangingOn hang td d
  /\ ~~ hangingOn hang td d'
  /\ isBefore td d /\ isBefore td d'.


Definition hft (hang : weekDay) (td : weekAndBefore) (d : weekDay) := True.

Definition hangingOnTodayIsReasoningAbout (hf : weekDay -> weekAndBefore -> weekDay -> Prop) hang td d : Prop :=
  (isOnOrAfter td hang -> hang = d) /\ ((isBefore td hang /\ isOnOrAfter td d) -> False)
  /\ (~(hf hang td d) -> ~(isBefore td hang /\ isBefore td d)).


Definition twoPossiblePRDXparam 
    (hangingOn : weekDay -> weekAndBefore -> weekDay -> Prop)
    (hang : weekDay) (td : weekAndBefore) :=
  (isOnOrAfter td hang /\ (hangingOn hang td hang) 
      /\ uniqueHanging_param (hangingOn hang td) hang dayBefore) 
  \/
  (isBefore td hang /\ noHangingYet_param hangingOn hang td 
      /\ twoPossible_param hangingOn hang td).


Definition hangingFuncOk : 
    forall hf, (forall hang td d, ~(hf hang td d) -> ~(isBefore td hang /\ isBefore td d)) ->
    forall hang td, 
    ~ (td = (someWeekDay thursday) /\ hang = friday) -> 
    twoPossiblePRDXparam (hangingOnTodayIsReasoningAbout hf) hang td.
Proof. 
  intros hf hfPrem. intros. assert (isBefore td hang \/ ~isBefore td hang).
  Focus 2. inversion H0. right. split; try tauto. 
  unfold hangingOnTodayIsReasoningAbout. split.
  intro. unfold isOnOrAfter. intro. intro. tauto.
  exists thursday. exists friday. split.
  intro. inversion H2. generalize (hfPrem hang td thursday). intro hft. 
  split. intro.
  apply H2. split; try split; try tauto.
  compute. tauto. 
  destruct td; try (destruct w); destruct hang; 
  compute in H2; compute in H; compute in H0; compute in H1; try tauto. 
  split. intro. generalize (hfPrem hang td friday). intro hff.
  destruct td; try (destruct w); destruct hang; 
  compute in H2; compute in H; compute in H0; compute in H1; try tauto. 
  destruct td; try (destruct w); destruct hang; 
  compute in H; compute in H0; compute in H1; try tauto. 
  left. split. compute; tauto.
  split. destruct hang; destruct td; try (destruct w); compute; try tauto.
  unfold hangingOnTodayIsReasoningAbout. intro. intros.
  assert (hang = d). tauto. rewrite <- H5.
  assert (hang = d'). tauto. rewrite <- H6.
  tauto. destruct td; try (destruct w); destruct hang; compute; try tauto.
Qed.


Lemma cantBeSurpFriday someHf : forall hang,
  twoPossiblePRDXparam someHf hang (someWeekDay thursday)
  -> noHangingYet_param someHf hang (someWeekDay thursday)
  -> False.
Proof.
  intros. destruct H. destruct H. destruct H1. 
  unfold noHangingYet_param in H0. generalize (H0 hang). tauto.
  assert (~twoPossible_param someHf hang (someWeekDay thursday)).
  compute. intro. destruct H1. destruct H1. destruct H1.
  generalize (H0 x). intro. destruct (H2). destruct H4. intro.
  unfold noHangingYet_param in H0. generalize (H0 x).
  generalize (H0 x0). intros. assert ( x0 = friday /\ x = friday).
  destruct x; destruct x0; compute in H6; compute in H7; compute; try tauto.
  destruct H8. rewrite H8 in H1. rewrite H9 in H1. tauto. tauto. 
Qed.

Definition onePossiblePRDXparam (hangingOn : weekDay -> weekAndBefore -> weekDay -> Prop) (hang : weekDay) (td : weekAndBefore) :=
  (isOnOrAfter td hang /\ (hangingOn hang td hang)
    /\ uniqueHanging_param (hangingOn hang td) hang dayBefore)
  \/
  (isBefore td hang /\ noHangingYet_param hangingOn hang td /\
    exists d, isBefore td d /\ ~~ (hangingOn hang td) d).


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
 
