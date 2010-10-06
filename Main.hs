{-# LANGUAGE TemplateHaskell #-}

module Main where

import Proof
import Tactic


environment [d|
    env = ()

    data Nat = Z | S Nat

    cata f xs = case xs of
        [] -> []
        x:xs -> f x : cata f xs

    len x = case x of
        [] -> 0
        x:xs -> 1 + len xs

    append a b = case a of
        [] -> b
        x:xs -> x : append xs b

    foldrr f z xs = case xs of
        [] -> z
        x:xs -> f x (foldrr f z xs)

    build g = g : []

    evenNat x = case x of
        Z -> True
        S x -> case x of
            Z -> False
            S x -> evenNat x

    doubleNat x = case x of
        Z -> Z
        S x -> S (S (doubleNat x))

    addNatAcc x y = case x of
        Z -> y
        S x -> addNatAcc x (S y)

    seqNat x res = case x of
        Z -> res
        S x -> seqNat x res

    propMapLength f x = len (cata f x) === len x

    propAssocAppend x y z = (x `append` y) `append` z === x `append` (y `append` z)

    propAppendNil x = x `append` [] === x
    
    propAppendIsAppend x y = append x y === append x y

    propEvenDouble x = seqNat x True === evenNat (doubleNat x)

    propEvenDoubleAcc x = seqNat x True === evenNat (addNatAcc x x)

    |]


main = do
    print proofAppendIsAppend
    print proofAppendNil
    print proofMapLength
    print proofAssocAppend
    print proofEvenDouble
    print proofEvenDoubleAcc

proofAppendIsAppend = prove env 'propAppendIsAppend none

proofAppendNil = prove env 'propAppendNil $ using
    [lhs $ defn env 'append
    ,lhs $ proofAppendNil
    ]

proofMapLength = prove env 'propMapLength $ using
    [lhs $ defn env 'len
    ,lhs $ defn env 'cata
    ,rhs $ defn env 'len
    ,lhs $ proofMapLength
    ]

proofAssocAppend = prove env 'propAssocAppend $ using
   [lhs $ defn env 'append
   ,lhs $ defn env 'append
   ,rhs $ defn env 'append
   ,rhs $ defn env 'append
   ,lhs $ proofAssocAppend
   ]

proofEvenDouble = prove env 'propEvenDouble $ using
    [rhs $ defn env 'evenNat
    ,rhs $ defn env 'doubleNat
    ,lhs $ defn env 'seqNat
    ,lhs $ proofEvenDouble
    ]

proofEvenDoubleAcc = prove env 'propEvenDoubleAcc $ using
    [rhs $ defn env 'evenNat
    ,rhs $ defn env 'addNatAcc
    ,lhs $ defn env 'seqNat
    ]
