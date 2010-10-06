{-# LANGUAGE PatternGuards #-}

module Proof(module Proof, module Type, module TH) where

import Type
import TH
import Data.Maybe
import Data.List
import Control.Monad
import Data.Generics.Uniplate.Data

data Lemma = Lemma Exp Exp

data QED = QED
    deriving Show

data Proof = Proof Lemma Strategy QED
    
data Side = Lhs | Rhs
    deriving (Show,Eq)

-- which side, how many matching expressions to skip (nearly always 0), and which lemma
data Action = Action Side Int Proof

data Strategy = Strategy [(Action,Strategy)]


instance Show Lemma where
    show (Lemma x y) = ppExp x ++ "===\n" ++ ppExp y

instance Show Proof where
    show (Proof x y z) = show x ++ show y ++ show z ++ "\n"

instance Show Action where
    show (Action a b (Proof c _ _)) = show a ++ " " ++ show b ++ "\n" ++ show c

instance Show Strategy where
    show (Strategy xs) = "{\n" ++ intercalate "|\n" [show a ++ unlines (map ("  "++) $ lines $ show b) | (a,b) <- xs] ++ "}\n"


infix  4 ===

prove :: Show a => Env -> a -> (Env -> Lemma -> Strategy) -> Proof
prove env name f = proof env lem (f env lem)
    where lem = toLemma env $ show name


defn :: Show a => Env -> a -> Proof
defn (Env env) x = maybe (error $ "Unknown definition: " ++ name)
        (\x -> Proof (Lemma (Var name) x) (Strategy []) QED) $ lookup name env
    where name = unqualify $ show x


(===) :: a -> a -> Bool
(===) a b = error "Can't run ===, should hook it up to QuickCheck"


toLemma :: Env -> String -> Lemma
toLemma (Env xs) x = maybe (error $ "Unknown lemma: " ++ unqualify x) f $ lookup (unqualify x) xs
    where f (Lam x y) = let Lemma a b = f y in Lemma (Lam x a) (Lam x b)
          f (Var "===" `App` x `App` y) = Lemma x y
          f x = error $ "Don't know how to make a lemma: " ++ show x


---------------------------------------------------------------------
-- PROOF CHECKING

proof :: Env -> Lemma -> Strategy -> Proof
proof env lem strat = Proof lem strat QED -- FIXME: Should check the proof is well formed before generating QED term


---------------------------------------------------------------------
-- EVALUATION BASED PROOF REDUCTION

reduce :: Lemma -> [Lemma]
reduce (Lemma x y) = [Lemma a b | (_,a,b) <- splitEval x y]

splitEval x y = split (eval x) (eval y)


eval :: Exp -> Exp
eval = transform f
    where
        f (App x y) = case eval x of
            Lam a b -> eval $ subst a y b
            x -> App x (eval y)
        f (Case (Con x y) ps) = head $ [eval $ substs (zip ps y) z | (Pat p ps,z) <- ps, p == x] ++ error "Case of Con, but no matching pattern"
        f x = x


joinForces :: [[(Var,Maybe [Pat])]] -> [(Var,Maybe [Pat])]
joinForces [] = []
joinForces xs = [(v, listToMaybe $ catMaybes r) | v <- map fst $ head xs, Just r <- [mapM (lookup v) xs]]


-- for case should also union if compatible down the alternatives
forced :: Exp -> [(Var,Maybe [Pat])]
forced (Var x) = [(x,Nothing)]
forced (Case (Var x) ps) = [(x,Just $ map fst ps)]
forced (Case x _) = forced x
forced _ = []


split :: Exp -> Exp -> [(Bool,Exp,Exp)] -- did you give out some information
split x y | x == y = []
split (Con x1 x2) (Con y1 y2) | x1 == y1 = concat $ zipWith splitEval x2 y2
split (Lam x1 x2) (Lam y1 y2) = splitEval x2 (subst y1 (Var x1) y2)

split x y | (v,Just ps):_ <- vs = concat [splitEval (subst v c x) (subst v c y) | Pat p ps <- ps, let c = Con p $ map Var ps]
    where vs = filter (isJust . snd) $ joinForces [forced x, forced y]

split x y = [(False,x,y)]


---------------------------------------------------------------------
-- APPLY AN ACTION

apply :: Action -> Lemma -> Maybe Lemma
apply (Action side _ (Proof lem@(Lemma l1 l2) _ _)) (Lemma a b)
    | side == Lhs = fmap (`Lemma` b) $ f a
    | side == Rhs = fmap (Lemma a) $ f b
    where f x = msum [fmap b $ apply0 lem a | (a,b) <- contexts x]


apply0 :: Lemma -> Exp -> Maybe Exp
apply0 (Lemma from to) x = do
    let (vs,frm) = fromLams from
    sub <- match vs frm x
    let unique x = length x == length (nub x)
    guard $ unique $ map fst $ nub sub
    return $ apps to [fromMaybe (Con "()" []) $ lookup v sub | v <- vs]


match :: [String] -> Exp -> Exp -> Maybe [(String,Exp)]
match fv (Var v) x | v `elem` fv = Just [(v,x)]
match fv x y | descend (const $ Var "") x == descend (const $ Var "") y =
    fmap concat $ sequence $ zipWith (match fv) (children x) (children y)
match fv _ _ = Nothing
