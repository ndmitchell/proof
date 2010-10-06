
module TH where

import Language.Haskell.TH
import Type

environment :: Q [Dec] -> Q [Dec]
environment x = do
    x <- x
    case map match x of
        Just n:_ -> return $ n (AppE (VarE $ mkName "read") $ LitE $ StringL $ show $ convert $ tail x) : tail x
        _ -> error "Expected a unit definition to bind to first"
    where
        match (ValD (VarP name) (NormalB (ConE unit)) _) | show unit == "GHC.Unit.()" =
            Just $ \x -> ValD (VarP name) (NormalB x) []
        match _ = Nothing
