{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

import Brick (defaultMain)
import Data.Proxy
import Magnifique.Typeable

import Decor.Soup
import Decor.Soup.Simple
import Decor.Types
import Decor.Utils

main =
  defaultMain
    magnifiqueApp
    (_unzip (Proxy @(CxOf X (Free (ChoiceF S1) S1))) treeH1)

deriving instance Generic (Free f a)

data X

type instance CxOf X a = F a

type family F a where
  F (DCore_ Soup) = NoCtx (DCore_ Soup)
--    F (Free f a) = EitherCx (Free f a) (CxOf X (f (Free f a))) (CxOf X a)
  F K1 = NoCtx K1
  F a = Blanket X a

instance IsContext (NoCtx (DCore_ Soup)) where
  type Full (NoCtx (DCore_ Soup)) = DCore_ Soup
  showRoot _ = showDCoreSoup
  showHole = undefined
  key = undefined
  down _ _ = Nothing
  cons = undefined


instance IsContext (NoCtx K1) where
  type Full (NoCtx K1) = K1
  showRoot _ = showK1
  showHole = undefined
  key = undefined
  down _ _ = Nothing
  cons = undefined

showDCoreSoup :: DCore_ Soup -> String
showDCoreSoup t = case t of
  Star -> "*"
  Var (DeBruijnV x) -> "|" ++ show x
  App t u rel -> show t ++ " " ++ show u ++ sRel rel
  Pi rel () u v -> "Π" ++ sRel rel ++ " " ++ show u ++ " -> " ++ show v
  Abs rel () u v -> "λ" ++ sRel rel ++ " " ++ show u ++ " . " ++ show v

sRel :: Rel -> String
sRel Rel = "+"
sRel Irr = "-"

showK1 :: K1 -> String
showK1 = undefined
