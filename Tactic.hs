{-# LANGUAGE TemplateHaskell #-}

module Tactic where

import Proof
import Control.Monad.State
import Data.Maybe
import Data.Char
import Debug.Trace


data Rule = Rule [Action] deriving Show

useAt a b c = Rule [Action a b c]
lhs = useAt Lhs 0
rhs = useAt Rhs 0
use x = Rule [Action Lhs 0 x, Action Rhs 0 x]


none :: Env -> Lemma -> Strategy
none = using [error "No rules given"]

rule x = "-- " ++ map toUpper x ++ " " ++ replicate (69 - 4 - length x) '-' ++ "\n"


using :: [Rule] -> Env -> Lemma -> Strategy
using acts env x = evalState (f x) acts
    where
        f :: Lemma -> State [Rule] Strategy
        f x = fmap Strategy $ case reduce x of
            [] -> return []
            xs -> mapM g xs

        g :: Lemma -> State [Rule] (Action, Strategy)
        g x = do
            () <- trace ("<TRACE>\n" ++ show x ++ "</TRACE>\n") $ return ()

            rs <- get
            () <- when (null rs) $ error $
                "\n" ++ rule "Failed" ++ "Ran out of rules\n" ++
                rule "Outstanding Lemma" ++ show x ++ rule "Failed"
            put $ tail rs
            let Rule as = head rs
            let (a,y) = head $ [(a,y) | a <- as, Just y <- [apply a x]] ++
                    [error $ "\n" ++ rule "Failed" ++ "Couldn't apply any rule\n" ++ 
                        concat [rule ("Rule " ++ show i) ++ show a | (i,a) <- zip [1..] as] ++
                        rule "Outstanding Lemma" ++ show x ++ rule "Failed"]
            res <- f y
            return (a,res)



automatic :: Env -> Lemma -> Strategy
automatic = none
