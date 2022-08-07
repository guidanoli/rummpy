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

Definition new_game (game : Game) : Prop :=
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
      ~ In card meld ->
      hand' = handl ++ handr ->
      hands' = tail hands ++ [hand'] ->
      meld' = card :: meld ->
      table' = tablel ++ [meld'] ++ tabler ->
      (table, hands, deck) --> (table', hands', deck)

where "g '-->' g'" := (step g g').

