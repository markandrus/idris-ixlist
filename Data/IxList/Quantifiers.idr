-- -------------------------------------------------- [ IxList/Quantifiers.idr ]
-- Module    : IxList/Quantifiers.idr
-- Copyright : (c) 2016 See CONTRIBUTORS.md
-- License   : see LICENSE.md
-- --------------------------------------------------------------------- [ EOH ]
module Data.IxList.Quantifiers

import Data.IxList

%access public export
%default total

||| A proof that some element of an IxList satisfies some property
|||
||| @ P the property to be satisfied
data Any : (P : t -> Type) -> IxList {t} xs -> Type where

  ||| A proof that the satisfying element is the first one in the `IxList`
  Here : {P : a -> Type} -> {xs : IxList xs'} -> P x -> Any P (x :: xs)

  ||| A proof that the satisfying element is in the tail of the `IxList`
  There : {P : a -> Type} -> {xs : IxList xs'} -> Any P xs -> Any P (x :: xs)

||| No element of an empty list satisfies any property
anyNilAbsurd : {P : a -> Type} -> Any P Nil -> Void
anyNilAbsurd (Here _) impossible
anyNilAbsurd (There _) impossible

implementation Uninhabited (Any p Nil) where
  uninhabited = anyNilAbsurd

||| Eliminator for `Any`
anyElim : {xs : IxList {t} xs'} -> {P : t -> Type} -> (Any P xs -> b) -> (P x -> b) -> Any P (x :: xs) -> b
anyElim _ f (Here p) = f p
anyElim f _ (There p) = f p

||| Given a decision procedure for a property, determine if an element of an
||| `IxList` satisfies it.
|||
||| @ P the property to be satisfied
||| @ dec the decision procedure
||| @ xs the `IxList` to examine
any : {P : t -> Type} -> (dec : (x : t) -> Dec (P x)) -> (xs : IxList {t} xs') -> Dec (Any P xs)
any _ Nil = No anyNilAbsurd
any p (x :: xs) with (p x)
  | Yes prf = Yes (Here prf)
  | No prf = case any p xs of
      Yes prf' => Yes (There prf')
      No prf' => No (anyElim prf' prf)

||| A proof that all elements of an `IxList` satisfy a property. It is an
||| `IxList` of proofs, corresponding element-wise to the `IxList`.
data All : (P : t -> Type) -> IxList {t} xs -> Type where
  Nil : {P : t -> Type} -> All P Nil
  (::) : {P : t -> Type} -> {xs : IxList {t} xs'} -> P x -> All P xs -> All P (x :: xs)


||| If there does not exist an element that satifies the property, then it is
||| the case that all elements do not satisfy.
negAnyAll : {P : t -> Type} -> {xs : IxList {t} xs'} -> Not (Any P xs) -> All (\x => Not (P x)) xs
negAnyAll {xs=Nil} _ = Nil
negAnyAll {xs=(x::xs)} f = (\x => f (Here x)) :: negAnyAll (\x => f (There x))

notAllHere : {P : t -> Type} -> {xs : IxList {t} xs'} -> Not (P x) -> All P (x :: xs) -> Void
notAllHere _ Nil impossible
notAllHere np (p :: _) = np p

notAllThere : {P : t -> Type} -> {xs : IxList {t} xs'} -> Not (All P xs) -> All P (x :: xs) -> Void
notAllThere _ Nil impossible
notAllThere np (_ :: ps) = np ps

||| Given a decision procedure for a property, decide whether all elements of
||| an `IxList` satisfy it.
|||
||| @ P the property
||| @ dec the decision procedure
||| @ xs the `IxList` to examine
all : {P : t -> Type} -> (dec : (x : t) -> Dec (P x)) -> (xs : IxList {t} xs') -> Dec (All P xs)
all _ Nil = Yes Nil
all d (x :: xs) with (d x)
  | No prf = No (notAllHere prf)
  | Yes prf = case all d xs of
      Yes prf' => Yes (prf :: prf')
      No prf' => No (notAllThere prf')
