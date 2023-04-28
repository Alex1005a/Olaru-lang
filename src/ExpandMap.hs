{-# LANGUAGE BangPatterns #-}
module ExpandMap where
import Data.Map ( Map, singleton, splitLookup )
import Data.Map.Internal
    ( Map(Bin, Tip), balanceL, balanceR, link )

insertWithRF :: (Applicative m, Ord k) => (a -> a -> m a) -> k -> a -> Map k a -> m (Map k a)
insertWithRF = go
  where
    go :: (Applicative m, Ord k) => (a -> a -> m a) -> k -> a -> Map k a -> m (Map k a)
    go _ !kx x Tip = pure $ singleton kx x
    go f !kx x (Bin sy ky y l r) =
        case compare kx ky of
            LT -> do
              (\m -> balanceL ky y m r) <$> go f kx x l
            GT -> do
              balanceR ky y l <$> go f kx x r
            EQ -> do
              (\v -> Bin sy ky v l r) <$> f y x

insertWithF :: (Applicative m, Ord k) => (a -> a -> m a) -> k -> a -> Map k a -> m (Map k a)
insertWithF = go
  where
    go :: (Applicative m, Ord k) => (a -> a -> m a) -> k -> a -> Map k a -> m (Map k a)
    go _ !kx x Tip =  pure $ singleton kx x
    go f !kx x (Bin sy ky y l r) =
        case compare kx ky of
            LT -> do
              (\m -> balanceL ky y m r) <$> go f kx x l
            GT -> do
              balanceR ky y l <$> go f kx x r
            EQ -> do
              (\v -> Bin sy kx v l r) <$> f y x

unionWithF :: (Applicative m, Ord k) => (a -> a -> m a) -> Map k a -> Map k a -> m (Map k a)
unionWithF _f t1 Tip = pure t1
unionWithF f t1 (Bin _ k x Tip Tip) = insertWithRF f k x t1
unionWithF f (Bin _ k x Tip Tip) t2 = insertWithF f k x t2
unionWithF _f Tip t2 = pure t2
unionWithF f (Bin _ k1 x1 l1 r1) t2 = case splitLookup k1 t2 of
  (l2, mb, r2) -> case mb of
      Nothing -> link k1 x1 <$> l1l2 <*> r1r2
      Just x2 -> link k1 <$> f x1 x2 <*> l1l2 <*> r1r2
    where !l1l2 = unionWithF f l1 l2
          !r1r2 = unionWithF f r1 r2