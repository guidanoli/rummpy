(* Rummy specification in Coq *)

From Coq Require Import Lists.List.
Import ListNotations.

Inductive Rank : Type :=
  | Ace
  | Two
  | Three
  | Four
  | Five
  | Six
  | Seven
  | Eight
  | Nine
  | Ten
  | Jack
  | Queen
  | King.

Definition rprev (rank : Rank) : Rank :=
  match rank with
  | Ace => King
  | Two => Ace
  | Three => Two
  | Four => Three
  | Five => Four
  | Six => Five
  | Seven => Six
  | Eight => Seven
  | Nine => Eight
  | Ten => Nine
  | Jack => Ten
  | Queen => Jack
  | King => Queen
  end.

Inductive Suit : Type :=
  | Clubs
  | Diamonds
  | Hearts
  | Spades.

Definition Card : Type := Rank * Suit.

Definition crank (card : Card) : Rank := fst card.

Definition csuit (card : Card) : Suit := snd card.

Definition before (c1 c2 : Card) : Prop :=
  crank c1 = rprev (crank c2).

Definition Meld : Type := list Card.

Fixpoint NoDuplicates (meld : Meld) : Prop :=
  match meld with
  | nil => True
  | card :: meld' => (~ In card meld') /\ NoDuplicates meld'
  end.

Definition is_set (rank : Rank) (meld : Meld) : Prop :=
  length meld >= 3 /\
  forall card, In card meld -> crank card = rank /\
  NoDuplicates meld.

Fixpoint Sequential (meld : Meld) : Prop :=
  match meld with
  | nil => True
  | card :: meld' => match meld' with
                     | card' :: _ => before card card' /\ Sequential meld'
                     | nil => True
                     end
  end.

Definition has_middle_ace (meld : Meld) : Prop :=
  exists card,
    In card (removelast (tail meld)) /\
    crank card = Ace.

Definition is_run (suit : Suit) (meld : Meld) : Prop :=
  length meld >= 3 /\
  forall card, In card meld -> csuit card = suit /\
  Sequential meld /\
  ~ has_middle_ace meld.

Definition is_valid_meld (meld : Meld) : Prop :=
  (exists rank, is_set rank meld) \/
  (exists suit, is_run suit meld).

Definition Deck : Type := list Card.

Definition Hand : Type := list Card.

Definition Table : Type := list Meld.

Definition Hands : Type := list Hand.

Definition Game : Type := Table * Hands * Deck.

Definition gdeck (game : Game) : Deck := snd game.

Definition ghands (game : Game) : Hands := snd (fst game).

Definition gtable (game : Game) : Table := fst (fst game).

Definition full_deck (deck : Deck) : Prop :=
  forall card, In card deck.

Definition initial (game : Game) : Prop :=
  (gdeck game = nil) /\
  (ghands game = nil) /\
  (gtable game = nil).

Definition is_curr (hand : Hand) (hands : Hands) : Prop :=
  value hand = head hands.

Fixpoint is_valid_table (table : Table) : Prop :=
  forall meld, In meld table -> is_valid_meld meld.

Definition lst_remove {A : Type} (a : A) (lst lst' : list A) : Prop :=
  exists left right, lst = left ++ a :: right /\ lst' = left ++ right.

Notation "lst '~' a '&' lst'" := (lst_remove a lst lst') (at level 30).

Theorem lst_remove_in :
  forall {A : Type} (a : A) lst lst', lst ~ a & lst' -> In a lst.
Proof.
  intros.
  unfold lst_remove in H.
  destruct H as [l [r [H H']]].
  rewrite H.
  apply in_or_app.
  right.
  apply in_eq.
Qed.

Theorem lst_remove_exists :
  forall {A : Type} (a : A) lst, In a lst -> exists lst', lst ~ a & lst'.
Proof.
  intros.
  unfold lst_remove.
  apply in_split in H.
  destruct H as [l1 [l2 H]].
  eauto.
Qed.

Theorem lst_remove_length :
  forall {A : Type} (a : A) lst lst', lst ~ a & lst' -> length lst = S (length lst').
Proof.
  intros.
  unfold lst_remove in H.
  destruct H as [l [r [H H']]].
  rewrite H, H'.
  repeat rewrite app_length.
  simpl. auto.
Qed.

Theorem lst_remove_not_nil :
  forall {A : Type} (a : A) lst lst', lst ~ a & lst' -> lst <> nil.
Proof.
  intros.
  apply lst_remove_in in H.
  unfold not.
  intro Hempty.
  rewrite Hempty in H.
  simpl in H.
  destruct H.
Qed.

Definition lst_replace {A : Type} (a a' : A) (lst lst' : list A) : Prop :=
  exists left right, lst = left ++ a :: right /\ lst' = left ++ a' :: right.

Notation "lst '~(' a ',' a' ')~>' lst'" := (lst_replace a a' lst lst') (at level 30).

Theorem lst_replace_in :
  forall {A : Type} (a a' : A) lst lst', lst ~( a, a' )~> lst' -> In a lst /\ In a' lst'.
Proof.
  intros.
  unfold lst_replace in H.
  destruct H as [l [r [H H']]].
  split;
  match goal with
    [ Hx: ?x = _ |- In _ ?x ] =>
        rewrite Hx;
        apply in_app_iff;
        right;
        apply in_eq
  end.
Qed.

Theorem lst_replace_exists :
  forall {A : Type} (a : A) lst, In a lst ->
  forall (a' : A), exists lst', lst ~( a, a' )~> lst'.
Proof.
  intros.
  apply in_split in H.
  destruct H as [l [r H]].
  exists (l ++ a' :: r).
  rewrite H.
  unfold lst_replace.
  eauto.
Qed.

Theorem lst_replace_length :
  forall {A : Type} (a a' : A) lst lst', lst ~( a, a' )~> lst' ->
  length lst = length lst'.
Proof.
  intros.
  unfold lst_replace in H.
  destruct H as [l [r [H H']]].
  rewrite H, H'.
  repeat rewrite app_length.
  simpl.
  trivial.
Qed.

Theorem lst_replace_not_nil :
  forall {A : Type} (a a' : A) lst lst', lst ~( a, a' )~> lst' ->
  lst <> nil /\ lst' <> nil.
Proof.
  intros.
  unfold lst_replace in H.
  destruct H as [l [r [H H']]].
  rewrite H, H'.
  split;
  match goal with
    [ Hx: _ = l ++ ?x :: r |- l ++ ?x :: r <> [] ] =>
        pose (app_cons_not_nil l r x)
  end;
  auto.
Qed.

Reserved Notation "t '-->?' t'" (at level 40).

Inductive table_step : Table -> Table -> Prop :=
  | split_meld :
      forall table table1 table2 table' meld meld1 meld2,
      table ~ meld & table1 -> (* remove a meld from table *)
      meld = meld1 ++ meld2 -> (* split the meld into two *)
      meld1 <> nil -> (* first meld must not be empty *)
      meld2 <> nil -> (* second meld must not be empty *)
      table2 ~ meld1 & table1 -> (* add first meld *)
      table' ~ meld2 & table2 -> (* add second meld *)
      table -->? table'
  | concat_melds :
      forall table table1 table2 table' meld1 meld2 meld,
      table ~ meld1 & table1 -> (* remove one meld from table *)
      table1 ~ meld2 & table2 -> (* remove another meld from table *)
      meld = meld1 ++ meld2 -> (* concatenate the melds *)
      table' ~ meld & table2 -> (* add the concatenated meld to table *)
      table -->? table'

where "t '-->?' t'" := (table_step t t').

Reserved Notation "t '-->?*' t'" (at level 40).

Inductive multi_table_step : Table -> Table -> Prop :=
  | no_table_step :
      forall t,
      t -->?* t
  | one_table_step :
      forall t t' t'',
      t -->?* t' ->
      t' -->? t'' ->
      t -->?* t''

where "t '-->?*' t'" := (multi_table_step t t').

Reserved Notation "g '-->' g'" (at level 40).

Inductive game_step : Game -> Game -> Prop :=
  | add_deck :
      forall table hands deck deck' deck'',
      full_deck deck' ->
      deck'' = deck ++ deck' ->
      (table, hands, deck) --> (table, hands, deck'')
  | welcome_player :
      forall table hands hands' deck deck' hand,
      length hand = 9 ->
      deck = hand ++ deck' ->
      hands' = hands ++ [hand] ->
      (table, hands, deck) --> (table, hands', deck')
  | draw_card :
      forall table hands hands' deck deck' hand card,
      is_curr hand hands ->
      deck = card :: deck' ->
      hands' = tail hands ++ [card :: hand] ->
      (table, hands, deck) --> (table, hands', deck')
  | add_set :
      forall table table' hands hands' deck hand hand1 hand2 hand'
             card1 card2 card3 meld rank,
      is_curr hand hands ->
      hand ~ card1 & hand1 ->
      hand1 ~ card2 & hand2 ->
      hand2 ~ card3 & hand' ->
      meld = [card1; card2; card3] ->
      is_set rank meld ->
      hands' = tail hands ++ [hand'] ->
      table' ~ meld & table ->
      (table, hands, deck) --> (table', hands', deck)
  | add_run :
      forall table table' hands hands' deck hand hand1 hand2 hand'
             card1 card2 card3 meld suit,
      is_curr hand hands ->
      hand ~ card1 & hand1 ->
      hand1 ~ card2 & hand2 ->
      hand2 ~ card3 & hand' ->
      meld = [card1; card2; card3] ->
      is_run suit meld ->
      hands' = tail hands ++ [hand'] ->
      table' ~ meld & table ->
      (table, hands, deck) --> (table', hands', deck)
  | add_card_to_set :
      forall table table' table'' hands hands' deck hand hand'
             card meld meld' rank,
      table -->?* table' ->
      is_valid_table table' ->
      is_curr hand hands ->
      hand ~ card & hand' ->
      crank card = rank ->
      is_set rank meld ->
      meld' ~ card & meld ->
      is_set rank meld' ->
      hands' = tail hands ++ [hand'] ->
      table' ~( meld, meld' )~> table'' ->
      (table, hands, deck) --> (table'', hands', deck)
  | add_card_to_run :
      forall table table' table'' hands hands' deck hand hand'
             card meld meld' suit,
      table -->?* table' ->
      is_valid_table table' ->
      is_curr hand hands ->
      hand ~ card & hand' ->
      csuit card = suit ->
      is_run suit meld ->
      meld' ~ card & meld ->
      is_run suit meld' ->
      hands' = tail hands ++ [hand'] ->
      table' ~( meld, meld' )~> table'' ->
      (table, hands, deck) --> (table'', hands', deck)

where "g '-->' g'" := (game_step g g').

Reserved Notation "g '-->*' g'" (at level 40).

Inductive multi_game_step : Game -> Game -> Prop :=
  | no_game_step :
      forall g,
      g -->* g
  | transitive_game_step :
      forall g g' g'',
      g -->* g' ->
      g' --> g'' ->
      g -->* g''

where "g '-->*' g'" := (multi_game_step g g').
