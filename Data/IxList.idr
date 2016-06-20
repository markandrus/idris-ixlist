-- -------------------------------------------------------------- [ IxList.idr ]
-- Module    : IxList.idr
-- Copyright : (c) 2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Data.IxList

%default total

||| A list indexed by its elements
||| @ t the type of elements contained within the IxList
data IxList : {t : Type} -> List t -> Type where

  ||| The empty IxList
  Nil : IxList []

  ||| Add an element to the IxList
  (::) : (x : t) -> IxList xs -> IxList (x :: xs)

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

||| Returns `True` iff the argument is empty
isNil : IxList ts -> Bool
isNil [] = True
isNil _  = False

||| Returns `True` iff the argument is not empty
isCons : IxList ts -> Bool
isCons [] = False
isCons _  = True

--------------------------------------------------------------------------------
-- Length
--------------------------------------------------------------------------------

length : IxList ts -> Nat
length [] = 0
length (x::xs) = 1 + length xs

--------------------------------------------------------------------------------
-- Indexing into IxLists
--------------------------------------------------------------------------------

||| All but the first element of the IxList
tail : IxList (t :: ts) -> IxList ts
tail (_ :: xs) = xs

||| Attempt to get the tail of an IxList. If the IxList is empty, return
||| `Nothing`.
tail' : IxList {t} xs -> Maybe (xs' : List t ** IxList xs')
tail' [] = Nothing
tail' (_ :: xs) = Just (_ ** xs)

||| Only the first element of the IxList
head : IxList (t :: ts) -> IxList [t]
head (x :: _) = [x]

||| Attempt to get the first element of an IxList. If the IxList is empty,
||| return `Nothing`.
head' : IxList {t} xs -> Maybe t
head' [] = Nothing
head' (x :: _) = Just x

||| The last element of the IxList
last : IxList {t} (x :: xs) -> t
last (x :: []) = x
last (x :: y :: ys) = last $ y :: ys

||| Attempt to get the last element of an IxList. If the IxList is empty, return
||| `Nothing`.
last' : IxList {t} xs -> Maybe (xs' : List t ** IxList xs')
last' [] = Nothing
last' (x :: xs) = case xs of
  []     => Just (_ ** [x])
  _ :: _ => last' xs

||| All but the last element of the IxList
init : IxList (t :: ts) -> IxList (init (t :: ts))
init (x :: []) = []
init (x :: y :: ys) = x :: init (y :: ys)

||| Attempt to get all but the last element of an IxList. If the IxList is
||| empty, return `Nothing`.
init' : IxList {t} xs -> Maybe (xs' : List t ** IxList xs')
init' [] = Nothing
init' (x :: xs) = case xs of
  []      => Just (_ ** [])
  y :: ys => case init' $ y :: ys of
    Nothing       => Nothing
    Just (_ ** j) => Just (_ ** x :: j)

--------------------------------------------------------------------------------
-- Sub-IxLists
--------------------------------------------------------------------------------

||| Take the first `n` elements of `xs`.
|||
||| If there are not enough elements, return the whole IxList.
||| @ n how many elements to take
||| @ xs the IxList to take them from
take : (n : Nat) -> (xs : IxList ts) -> IxList (take n ts)
take Z     _         = []
take (S n) []        = []
take (S n) (x :: xs) = x :: take n xs

||| Drop the first `n` elements of `xs`.
|||
||| If there are not enough elements, return the empty IxList.
||| @ n how many elements to drop
||| @ xs the IxList to drop them from
drop : (n : Nat) -> (xs : IxList ts) -> IxList (drop n ts)
drop Z     xs        = xs
drop (S n) []        = []
drop (S n) (x :: xs) = drop n xs

||| Take the longest prefix of an IxList such that all elements satisfy some
||| Boolean predicate.
|||
||| @ p the predicate
takeWhile : (p : t -> Bool) -> IxList {t} xs -> IxList (takeWhile p xs)
takeWhile _ [] = []
takeWhile p (x :: xs) with (p x)
  takeWhile p (x :: xs) | True = x :: takeWhile p xs
  takeWhile p (x :: xs) | False = []

||| Remove the longest prefix of an IxList such that all removed elements
||| satisfy some Boolean predicate.
|||
||| @ p the predicate
dropWhile : (p : t -> Bool) -> IxList {t} xs -> IxList (dropWhile p xs)
dropWhile _ [] = []
dropWhile p (x :: xs) with (p x)
  dropWhile p (x :: xs) | True = dropWhile p xs
  dropWhile p (x :: xs) | False = x :: xs

--------------------------------------------------------------------------------
-- Building (bigger) IxLists
--------------------------------------------------------------------------------

||| Append two IxLists
(++) : IxList as -> IxList bs -> IxList (as ++ bs)
(++) []      right = right
(++) (x::xs) right = x :: (xs ++ right)

||| Construct an IxList with `n` copies of `x`
||| @ n how many copies
||| @ x the element to replicate
replicate : (n : Nat) -> (x : t) -> IxList (replicate n x)
replicate Z     x = []
replicate (S n) x = x :: replicate n x
