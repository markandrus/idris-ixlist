-- -------------------------------------------------------------- [ IxList.idr ]
-- Module    : IxList.idr
-- Copyright : (c) 2016 See CONTRIBUTORS.md
-- License   : see LICENSE.md
-- --------------------------------------------------------------------- [ EOH ]
module Data.IxList

import Data.List

%access public export
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

||| Compute the length of an IxList.
|||
||| Runs in linear time
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
  | True = x :: takeWhile p xs
  | False = []

||| Remove the longest prefix of an IxList such that all removed elements
||| satisfy some Boolean predicate.
|||
||| @ p the predicate
dropWhile : (p : t -> Bool) -> IxList {t} xs -> IxList (dropWhile p xs)
dropWhile _ [] = []
dropWhile p (x :: xs) with (p x)
  | True = dropWhile p xs
  | False = x :: xs

--------------------------------------------------------------------------------
-- Building (bigger) IxLists
--------------------------------------------------------------------------------

||| Append two IxLists
(++) : IxList as -> IxList bs -> IxList (as ++ bs)
(++) []        right = right
(++) (x :: xs) right = x :: (xs ++ right)

||| Construct an IxList with `n` copies of `x`
||| @ n how many copies
||| @ x the element to replicate
replicate : (n : Nat) -> (x : t) -> IxList (replicate n x)
replicate Z     _ = []
replicate (S n) x = x :: replicate n x

--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------

||| Combine two IxLists element-wise using some function. If they are different
||| lengths, the result is truncate to the length of the shorter IxList.
||| @ f the function to combine elements with
||| @ l the first IxList
||| @ r the second IxList
zipWith : (f : a -> b -> c)
       -> (l : IxList xs)
       -> (r : IxList ys)
       -> IxList (zipWith f xs ys)
zipWith _ []        (_ :: _)  = []
zipWith _ (_ :: _)  []        = []
zipWith _ []        []        = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

-- TODO: Figure out why this doesn't typecheck.
-- ||| Combine three IxLists element-wise using some function. If they are
-- ||| different lengths, the result is truncated to the length of the shortest
-- ||| IxList.
-- ||| @ f the function to combine elements with
-- ||| @ x the first IxList
-- ||| @ y the second IxList
-- ||| @ z the third IxList
-- zipWith3 : (f : a -> b -> c -> d)
--         -> (x : IxList xs)
--         -> (y : IxList ys)
--         -> (z : IxList zs)
--         -> IxList (zipWith3 f xs ys zs)
-- zipWith3 f _         []        (_ :: _)  = []
-- zipWith3 f _         (_ :: _)  []        = []
-- zipWith3 f []        (_ :: _)  _         = []
-- zipWith3 f (_ :: _)  []        _         = []
-- zipWith3 f []        []        []        = []
-- zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

||| Combine two IxLists element-wise into pairs
zip : (l : IxList as) -> (r : IxList bs) -> IxList (zip as bs)
zip = zipWith (\x, y => (x, y))

-- TODO: Uncomment this once zipWith3 works.
-- ||| Combine three IxLists element-wise into tuples
-- zip3 : (x : IxList as) -> (y : IxList bs) -> (z : IxList cs) -> IxList (zip3 as bs cs)
-- zip3 = zipWith3 (\x, y, z => (x, y, z))

||| Split an an IxList of pairs into two IxLists
unzip : IxList {t=(a, b)} xs
     -> (IxList (map Prelude.Basics.fst xs),
         IxList (map Prelude.Basics.snd xs))
unzip [] = ([], [])
unzip ((l, r) :: xs) with (unzip xs)
  | (lefts, rights) = (l :: lefts, r :: rights)

-- TODO: Add unzip3 once zip3 works.

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

||| Apply a partial function to the elements of an IxList, keeping the ones at
||| which it is defined.
mapMaybe : (f : a -> Maybe b) -> IxList xs -> IxList (mapMaybe f xs)
mapMaybe _ [] = []
mapMaybe f (x :: xs) with (f x)
  | Nothing = mapMaybe f xs
  | Just j  = j :: mapMaybe f xs


--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

-- TODO: Foldable

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

-- TODO: toIxList

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

-- TODO: reverse

-- TODO: Figure out why this doesn't typecheck.
-- ||| Insert some separator between the elements of an IxList.
-- intersperse : (a : t) -> IxList {t} as -> IxList (intersperse a as)
-- intersperse _ [] = []
-- intersperse sep (x :: xs) = x :: intersperse' sep xs where
--   intersperse' sep []      = []
--   intersperse' sep (y::ys) = sep :: y :: intersperse' sep ys

-- TODO: intercalate

-- TODO: transpose

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

||| Check if something is a member of an IxList using a custom comparison.
elemBy : (t -> t -> Bool) -> t -> IxList {t} ts -> Bool
elemBy _ _ [] = False
elemBy p e (x :: xs) = if p e x then True else elemBy p e xs

||| Check if something is a member of an IxList using the default Boolean
||| equality.
elem : Eq t => t -> IxList {t} ts -> Bool
elem = elemBy (==)

||| Find associated information in an IxList using a custom comparison.
lookupBy : (a -> a -> Bool) -> a -> IxList {t=(a, b)} xs -> Maybe b
lookupBy _ _ [] = Nothing
lookupBy p e (x :: xs) = let (l, r) = x in if p e l
  then Just r
  else lookupBy p e xs

||| Find associated information in an IxList using Boolean equality.
lookup : Eq a => a -> IxList {t=(a, b)} xs -> Maybe b
lookup = lookupBy (==)

||| Check if any elements of the first IxList are found in the second, using
||| a custom comparison.
hasAnyBy : (t -> t -> Bool) -> IxList {t} xs -> IxList {t} ys -> Bool
hasAnyBy _ _ [] = False
hasAnyBy p elems (x::xs) = if elemBy p x elems
  then True
  else hasAnyBy p elems xs


||| Check if any elements of the first IxList are found in the second, using
||| Boolean equality.
hasAny : Eq t => IxList {t} xs -> IxList {t} ys -> Bool
hasAny = hasAnyBy (==)

||| A proof that some element is found in an IxList.
data Elem : t -> IxList {t} ts -> Type where

  ||| A proof that the element is at the front of the IxList.
  Here : IxList.Elem x (x :: xs)

  ||| A proof that the element is after the front of the IxList.
  There : (later : IxList.Elem x xs) -> Elem x (y :: xs)

Uninhabited (Elem {t} x []) where
  uninhabited Here impossible
  uninhabited (There _) impossible

||| Is the given element a member of the given IxList?
|||
||| @ x the element to be tested
||| @ xs the IxList to be checked against
isElem : DecEq t => (x : t) -> (xs : IxList ts) -> Dec (Elem x xs)
isElem _ [] = No absurd
isElem x (y :: xs) with (decEq x y)
  isElem x (x :: xs) | Yes Refl = Yes Here
  isElem x (y :: xs) | No contra with (isElem x xs)
    isElem x (y :: xs) | No contra | Yes prf = Yes (There prf)
    isElem x (y :: xs) | No contra | No f = No (mkNo contra f) where
      mkNo : {xs' : IxList a}
          -> (x' = y' -> Void)
          -> (Elem x' xs' -> Void)
          -> Elem x' (y' :: xs')
          -> Void
      mkNo f _ Here = f Refl
      mkNo _ g (There x) = g x

--------------------------------------------------------------------------------
-- Misc.
--------------------------------------------------------------------------------

-- TODO: Implement me.
-- ||| Remove the element at the given position.
-- |||
-- ||| @ xs the IxList to be removed from
-- ||| @ p a proof that the element to be removed is in the IxList

-- TODO: Implement me.
-- ||| The intersectBy function returns the intersect of two IxLists by a
-- ||| user-supplied equality predicate.
-- intersectBy : (p : a -> a -> Bool)
--            -> IxList as
--            -> IxList bs
--            -> IxList (Data.List.intersectBy p as bs)
-- intersectBy eq xs ys = [x | x <- xs, any (eq x) ys]

-- TODO: Implement me.
-- ||| Compute the intersection of two IxLists according to their `Eq`
-- ||| implementation.
-- intersect : Eq t => IxList {t} as -> IxList bs -> IxList (intersect as bs)
-- intersect = intersectBy (==)
