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
  (full_deck (gdeck game)) /\
  (ghands game = nil) /\
  (gtable game = nil).

Definition is_curr (hand : Hand) (hands : Hands) : Prop :=
  value hand = head hands.

Reserved Notation "g '-->' g'" (at level 40).

Inductive step : Game -> Game -> Prop :=
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
  | add_card_to_set :
      forall table table' hands hands' deck hand hand' handl handr
             card meld meld' tablel tabler rank,
      is_curr hand hands ->
      hand = handl ++ [card] ++ handr ->
      crank card = rank ->
      table = tablel ++ [meld] ++ tabler ->
      is_set rank meld ->
      meld' = card :: meld ->
      is_set rank meld' ->
      hand' = handl ++ handr ->
      hands' = tail hands ++ [hand'] ->
      table' = tablel ++ [meld'] ++ tabler ->
      (table, hands, deck) --> (table', hands', deck)
  | add_card_to_run :
      forall table table' hands hands' deck hand hand' handl handr
             card meld meldl meldr meld' tablel tabler suit,
      is_curr hand hands ->
      hand = handl ++ [card] ++ handr ->
      csuit card = suit ->
      table = tablel ++ [meld] ++ tabler ->
      is_run suit meld ->
      meld = meldl ++ meldr ->
      meld' = meldl ++ [card] ++ meldr ->
      is_run suit meld' ->
      hand' = handl ++ handr ->
      hands' = tail hands ++ [hand'] ->
      table' = tablel ++ [meld'] ++ tabler ->
      (table, hands, deck) --> (table', hands', deck)

where "g '-->' g'" := (step g g').

Reserved Notation "g '-->*' g'" (at level 40).

Inductive multistep : Game -> Game -> Prop :=
  | one_step :
      forall g g',
      g --> g' ->
      g -->* g'
  | transitive_step :
      forall g g' g'',
      g -->* g' ->
      g' --> g'' ->
      g -->* g''

where "g '-->*' g'" := (multistep g g').

Definition valid (g' : Game) : Prop :=
  exists g, initial g /\ g -->* g'.
