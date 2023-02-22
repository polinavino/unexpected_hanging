

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
  ((exists d, isOnOrAfter td d /\ hangingOnDay d) /\ uniqueHanging dayBefore)
  \/
  (noHangingYet td /\ exists d, isBefore td d /\ ~~ hangingOnDay d).


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

Definition twoPossiblePRDX_param 
    (hangingOn : weekDay -> weekAndBefore -> weekDay -> Prop)
    (hang : weekDay) (td : weekAndBefore) :=
  (isOnOrAfter td hang /\ (hangingOn hang td hang) 
      /\ uniqueHanging_param (hangingOn hang td) hang dayBefore) 
  \/
  (isBefore td hang /\ noHangingYet_param hangingOn hang td 
      /\ twoPossible_param hangingOn hang td).

Definition hf (hang : weekDay) (td : weekAndBefore) (d : weekDay) := True.

Definition hangingOnTodayIsReasoningAbout hang td d : Prop :=
  (isOnOrAfter td hang -> hang = d) /\ ((isBefore td hang /\ isOnOrAfter td d) -> False)
  /\ ((isBefore td hang /\ isBefore td d) -> (~~ hf hang td d)).

Definition hangingFuncOk : forall hang td,
    ~ (td = (someWeekDay thursday) /\ hang = friday) -> 
    twoPossiblePRDX_param hangingOnTodayIsReasoningAbout hang td.
Proof. 
  intros. assert (isBefore td hang \/ ~isBefore td hang).
  Focus 2. inversion H0. right. split; try tauto. 
  unfold hangingOnTodayIsReasoningAbout. split.
  intro. unfold isOnOrAfter. intro. intro. tauto.
  exists thursday. exists friday. split.
  intro. inversion H2. unfold hf. split. intro.
  apply H2. split; try split; try tauto.
  compute. tauto. 
  destruct td; try (destruct w); destruct hang; 
  compute in H2; compute in H; compute in H0; compute in H1; try tauto. 
  split. intro.
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


Definition hangingOnTodayIsReasoningAbout_param realHF hang td d : Prop :=
  (isOnOrAfter td hang -> hang = d) /\ ((isBefore td hang /\ isOnOrAfter td d) -> False)
  /\ ((isBefore td hang /\ isBefore td d) -> (~ realHF hang td d)).

Definition hangingFuncOk_param realHF : forall hang td, realHF = hangingOnTodayIsReasoningAbout_param realHF ->
    ~ (td = (someWeekDay thursday) /\ hang = friday) -> 
    twoPossiblePRDX_param (hangingOnTodayIsReasoningAbout_param realHF) hang td.
Proof. 
  intros hang td rhf H. assert (isBefore td hang \/ ~isBefore td hang).
  Focus 2. inversion H0. right. split; try tauto. 
  unfold hangingOnTodayIsReasoningAbout. split.
  intro. unfold isOnOrAfter. intro. intro. 
  generalize H3. intro rhfrec.
  rewrite rhf in H3. 
  unfold hangingOnTodayIsReasoningAbout_param in H3.
  destruct H3. destruct H4. destruct H5.
  unfold hangingOnTodayIsReasoningAbout_param in rhfrec.
  tauto.
  unfold hangingOnTodayIsReasoningAbout_param in rhfrec.
  tauto.
  exists thursday. exists friday. split.
  intro. inversion H2. split. intro.
  generalize H2. intro rhfrec.
  rewrite rhf in H2. 
  unfold hangingOnTodayIsReasoningAbout_param in H2.
  apply rhfrec. 
  unfold hangingOnTodayIsReasoningAbout_param.
  destruct H2. 
  unfold hangingOnTodayIsReasoningAbout_param in rhfrec.
  split. intro. unfold isOnOrAfter in H2. tauto.
  split. 
  destruct td; try (destruct w); destruct hang; compute;
  compute in H; compute in H0; compute in H1; compute in rhfrec; try tauto.
  intros. intro. tauto. split.
  intro.
  generalize H2. intro rhfrec.
  rewrite rhf in H2. 
  unfold hangingOnTodayIsReasoningAbout_param in H2.
  apply rhfrec. 
  unfold hangingOnTodayIsReasoningAbout_param.
  destruct H2. 
  unfold hangingOnTodayIsReasoningAbout_param in rhfrec.
  split. intro. unfold isOnOrAfter in H2. tauto.
  split. 
  destruct td; try (destruct w); destruct hang; compute;
  compute in H; compute in H0; compute in H1; compute in rhfrec; try tauto.
  intros. intro. tauto. split;
  destruct hang; destruct td; try (destruct w); compute; try tauto.
  left. split. compute; tauto.
  split. destruct hang; destruct td; try (destruct w); compute; try tauto.
  unfold hangingOnTodayIsReasoningAbout_param. intro. intros.
  assert (hang = d). tauto. rewrite <- H5.
  assert (hang = d'). tauto. rewrite <- H6.
  tauto. destruct td; try (destruct w); destruct hang; compute; try tauto.
Qed.

Lemma cantBeSurpFriday someHf : forall hang,
  twoPossiblePRDX_param someHf hang (someWeekDay thursday)
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

Lemma twoNotUnique :
  forall td,
  twoPossible td ->
  ~ uniqueHanging td.
Proof.
  unfold twoPossible; unfold uniqueHanging; intros.
  intro. destruct H. destruct H. destruct H.
  generalize (H0 x x0). tauto.
Qed.

Lemma existsFuture td : twoPossiblePRDX td -> exists d, hangingOnDay d.
Proof.
intro. elim H. Focus 2. intro. destruct H0.
destruct H1. unfold noHangingYet in H0. destruct H1. elim (H0 x).
Focus 2. destruct H1. destruct H2. elim H2. intro. apply H1. tauto.

Lemma notBoth
    (td : weekAndBefore)  :
  (((exists d, isOnOrAfter td d /\ hangingOnDay d) /\ uniqueHanging dayBefore)
  /\
  (noHangingYet td /\ twoPossible td)) -> False.
Proof.
  generalize (twoNotUnique td).
  assert (uniqueHanging dayBefore -> uniqueHanging td).
  unfold uniqueHanging. intros. apply (H d d').
  compute. auto. auto. auto. tauto.
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
  ((exists d, isOnOrAfter td d /\ hangingOn d) /\ uniqueHanging_param hangingOn dayBefore)
  \/
  (noHangingYet_param hangingOn td /\ twoPossible_param hangingOn td).
 (*   ~ uniqueHanging_param hangingOn td). *)

(*
Lemma notUnique : forall td, ((exists d, hangingOnDay d)
    -> uniqueHanging dayBefore) -> (((isBefore td friday /\ noHangingYet td) ->
    twoPossible td) <-> ((isBefore td friday /\ noHangingYet td) ->
    ~ uniqueHanging td)).
Proof.
  intros td uni. split; unfold noHangingYet; unfold twoPossible; unfold uniqueHanging; intros.
  intro. generalize (H H0). intro. destruct H2. destruct H2. destruct H2. 
  generalize (dayEqDec x x0). generalize (H1 x x0). tauto. 
  assert (mt : ~uniqueHanging dayBefore -> ~(exists d : weekDay, hangingOnDay d)). tauto.
  elim mt. unfold uniqueHanging. intro. apply H. tauto.
  intros. apply H1; try tauto. destruct d; destruct d'; compute; try tauto.
Admitted. *)
  

Definition hangingOnTodayIsReasoningAbout hang td d : Prop := 
  (isOnOrAfter td hang -> hang = d) /\ (isBefore td hang /\ isBefore td d -> False)
  /\ (isBefore td hang /\ isOnOrAfter td d -> False).
    (*  -> ~~(realHF hang td d)). *)

Lemma sameNo : ~(exists d, hangingOnDay d) <-> forall d, ~hangingOnDay d.
Proof. 
  split; intro. intros. intro. elim H. exists d. auto.
  intro. destruct H0. elim (H x). tauto.
Qed.


Lemma bad (chf : weekDay -> weekAndBefore -> weekDay -> Prop) : 
      ~twoPossiblePRDX_param (chf monday dayBefore) dayBefore.
Proof.
intros. intro. destruct H. destruct H0. compute in H1.
assert (True /\
     (forall d : weekDay, (True -> False) -> chf monday dayBefore d -> False) ). tauto.
generalize (H1 H2). intros. destruct H3. destruct H3. destruct H3.
destruct H4. apply H4. intro. destruct H5.
 apply H5. intros. apply H3.  apply H0. 
exists x; tauto. tauto.
tauto. tauto.


split. unfold twoPossiblePRDX_param. in H. destruct H. destruct H0.
assert (twoPossible dayBefordestruct H1.e  -> ~uniqueHanging dayBefore).
apply twoNotUnique.
assert (twoPossible dayBefore -> ~(exists d : weekDay, hangingOnDay d) ). tauto. 
assert (twoPossible dayBefore -> ~~ (exists d : weekDay, hangingOnDay d)).
intro. destruct H4. destruct H4.  intro. elim H5.
destruct H4. destruct H6. exists x. elim H6. intro. apply H6.  tauto. apply H4.
unfold twoPossible in H3. *)

Lemma hangingFuncOk : forall hang td, 
  ~ (td <> (someWeekDay thursday) /\ hang = friday)  
  -> twoPossiblePRDX_param (hangingOnTodayIsReasoningAbout hang td) td.
Proof.
  intros. split. intro. exists hang. split.
  tauto. rewrite H0. compute. tauto. 
  unfold hangingOnTodayIsReasoningAbout. split.
  intros. intro. intros. unfold isOnOrAfter in H3. unfold isOnOrAfter in H2.
  assert (dec : isBefore td hang \/ ~isBefore td hang).
  destruct td; try compute; try tauto.
  destruct w, hang; intuition discriminate. inversion dec.
  destruct H2. destruct H3.
  
 intro. intros.
  destruct H4. destruct H3. assert (dec : isOnOrAfter td hang \/ ~isOnOrAfter td hang).
  destruct td; try compute; try tauto.
  destruct w, hang; intuition discriminate. inversion dec.
  rewrite  <- (H3 H7). rewrite <- (H4 H7). auto.
  unfold isOnOrAfter in H7. 
  rewrite H in H5. unfold hangingOnTodayIsReasoningAbout in H5.
  
Focus 2. intros. intro. destruct H1. unfold uniqueHanging_param in H2.
  unfold hangingOnTodayIsReasoningAbout in H2.

elim H6; try tauto.
  assert (decB : isBefore td hang \/ ~isBefore td hang).
  destruct td; try compute; try tauto.
  destruct w, hang; intuition discriminate.  
  split; try tauto. tauto.

  generalize (dayEqDec d d'). intro. inversion H5. auto.
  elim H6.
  
  intros. intro. intros.


destruct hang; compute; try tauto;
  destruct td; try (destruct d); compute;  try split; try split; try tauto; try (intros g); 
  try (inversion g); try intros; try (destruct d); 
  try (destruct d'); try (exists monday); auto.
  
  assert (mta : ~~monday = tuesday -> monday = tuesday).
  generalize (dayEqDec monday tuesday). tauto. apply mta. intro.

  intro mt. inversion mt. auto. elim H5.
  elim H4. intros. elim H6. auto. intro.
  rewrite H in H7. unfold  hangingOnTodayIsReasoningAbout in H7.
  
   intros; ; try tauto.

  rewrite H in H4.
  Focus 171.
  assert (mt : ~ realHF monday dayBefore monday).
  rewrite H. intro. rewrite H in H5.
  inversion H.
  destruct H1. 

; try (intros Hd); try (inversion Hd). split. intros H. inversion H.
  split. intros.

Fixpoint constraints (td: weekAndBefore) (d : weekDay) : Prop :=
  match td with
  | _ => True
  end.

Lemma existsHangFunc td :
  exists (hangingOn : weekDay -> Prop), 
  td <> (someWeekDay thursday) 
  -> twoPossiblePRDX_param hangingOn td.
Proof.
exists (constraints td). compute. intro.
elim H.
  destruct td.
  split; try split; destruct td; compute. split. split.

Inductive weekDay :=
| sunday : weekDay
| monday : weekDay
| tuesday : weekDay
| wednesday : weekDay
| thursday : weekDay
| friday : weekDay
| saturday : weekDay.



Definition paradoxConstraints (h : weekDay -> Prop) (td : weekDay) := h td.

Lemma haveHangingFunc : exists (hangingOn : weekDay -> Prop),
  forall (td:weekDay), td <> friday -> paradoxConstraints hangingOn td.
Proof.
  exists constraints.
  unfold constraints,paradoxConstraints.
  intros td; elim td.
