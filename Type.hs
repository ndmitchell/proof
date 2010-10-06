{-# LANGUAGE DeriveDataTypeable #-}

module Type where

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH hiding (Con,Exp,Pat)
import qualified Language.Haskell.Exts as HSE
import Data.Data

type Var = String
type Con = String

data Exp = Case Exp [(Pat,Exp)]
         | App Exp Exp
         | Var Var
         | Lam Var Exp
         | Lit String
         | Con Con [Exp]
           deriving (Read,Show,Eq,Data,Typeable)

data Pat = Pat Con [Var]
           deriving (Read,Show,Eq,Data,Typeable)

data Env = Env [(Var,Exp)]
           deriving (Read,Show,Eq,Data,Typeable)


ppExp :: Exp -> String
ppExp x = HSE.prettyPrint (f x) ++ "\n"
    where
--        f (Let a b c) = HSE.Let (HSE.BDecls [HSE.PatBind sl (pvar a) Nothing (HSE.UnGuardedRhs $ f b) (HSE.BDecls [])]) $ f c
        f (Case a b) = HSE.Case (f a) (map g b)
        f (App a b) = HSE.App (f a) (f b)
        f (Var x) = HSE.Var $ HSE.UnQual $ HSE.Ident x
        f (Lam v x) = HSE.Lambda sl [pvar v] (f x)
        f (Con x xs) = f $ apps (Var x) xs
        f (Lit x) = f $ Var x

        -- g (Default, x) = HSE.Alt sl HSE.PWildCard (HSE.UnGuardedAlt $ f x) (HSE.BDecls [])
        g (Pat c xs, x) = HSE.Alt sl (HSE.PApp (HSE.UnQual $ HSE.Ident c) $ map pvar xs) (HSE.UnGuardedAlt $ f x) (HSE.BDecls [])

        pvar = HSE.PVar . HSE.Ident
        sl = HSE.SrcLoc "" 0 0


apps x [] = x
apps x (y:ys) = apps (App x y) ys

lams [] x = x
lams (v:vs) x = Lam v (lams vs x)

fromLams (Lam v x) = let (a,b) = fromLams x in (v:a,b)
fromLams x = ([], x)


subst :: Var -> Exp -> Exp -> Exp
subst a b x = case x of
--    Let v x y | a /= v -> Let v (f x) (f y)
    Case x xs -> Case (f x) (map g xs)
    App x y -> App (f x) (f y)
    Var x -> if x == a then b else Var x
    Lam v x | a /= v -> Lam v $ f x
    Con c xs -> Con c $ map f xs
    _ -> x
    where
        f = subst a b
        --g (Default, x) = (Default, f x)
        g (Pat c vs, x) = (Pat c vs, if a `elem` vs then x else f x)


substs :: [(Var,Exp)] -> Exp -> Exp
substs [] x = x
substs ((a,b):vs) x = substs vs $ subst a b x


convert :: [TH.Dec] -> Env
convert xs = Env $ concatMap dec xs
    where
        dec (FunD name [x]) = [(show name, clause x)]
        dec DataD{} = []
        dec x = error $ "convert dec: " ++ show x

        clause (Clause ps (NormalB x) []) = exp $ LamE ps x
        clause x = error $ "convert clause: " ++ show x

        exp (LamE [] x) = exp x
        exp (LamE (v:vs) x) = Lam (varp v) $ exp $ LamE vs x
        exp (CaseE x y) = Case (exp x) (map match y)
        exp (VarE x) = Var $ fromName x
        exp (ConE x) = lams as $ Con (fromName x) $ map Var as
            where as = ["v" ++ show i | i <- [1 .. arity $ fromName x]]
        exp (InfixE (Just x) y (Just z)) = exp y `App` exp x `App` exp z
        exp (AppE x y) = App (exp x) (exp y)
        exp (LitE x) = Lit $ show x
        exp x = error $ "convert exp: " ++ show x

        match (Match p (NormalB x) []) = (pat p, exp x)
        match x = error $ "convert match: " ++ show x

        pat (InfixP x y z) = pat $ ConP y [x,z]
        pat (ConP x ys) = Pat (fromName x) (map varp ys)
        pat x = error $ "convert pat: " ++ show x

        varp (VarP x) = fromName x
        varp x = error $ "convert varp: " ++ show x


arity x | x `elem` words "[] True False Z" = 0
arity x | x `elem` words "S" = 1
arity x | x `elem` words ":" = 2
arity x = error $ "Arity not known for: " ++ show x


unqualify :: String -> String
unqualify = reverse . takeWhile (/= '.') . reverse

fromName :: Name -> String
fromName = unqualify . show
