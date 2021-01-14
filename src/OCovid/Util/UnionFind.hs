module OCovid.Util.UnionFind where

import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Maybe as Maybe

type UnionFind a = Map a a

find :: Ord t => UnionFind t -> t -> t
find m k
    | not $ k `Map.member` m = k
    | Map.lookup k m == Just k = k
    | otherwise = find m (Maybe.fromJust (Map.lookup k m))
    
union :: Ord k => UnionFind k -> k -> k -> UnionFind k
union m a b =
    let a' = find m a
        m' = Map.insert a a' (Map.insert b a' m)
    in m'
