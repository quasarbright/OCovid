module OCovid.Util.Phase where

data Phase a b err =
    Phase { phaseName :: String
          , f :: a -> Either err b
          }

data Config =
    Config { shouldPrint :: Bool
           , finalPhase :: Maybe String
           }