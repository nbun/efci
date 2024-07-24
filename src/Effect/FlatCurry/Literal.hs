{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.FlatCurry.Literal where

import Curry.FlatCurry.Type (Literal (..))
import Free
import Signature

data Lit a
  = FLit Literal
  | External [a] ([Literal] -> a)
  deriving (Functor)

lit :: (Lit :<: sig) => Literal -> Prog (Sig sig sigs sigl l) v
lit l = Call (A (Algebraic (inj (FLit l))))

runLit
  :: forall sig sigs sigl l a
   . (Functor sig, Functor sigs)
  => Prog (Sig (Lit :+: sig) sigs sigl l) a
  -> Prog (Sig sig sigs sigl (EitherL l)) (Either Literal a)
runLit = unEL . fold point (aalg algL)
 where
  algL :: Lit (EL sig sigs sigl l x) -> EL sig sigs sigl l x
  algL (FLit l) = EL (return (Left l))
  algL (External ps k) = EL $ do
    xs <- mapM unEL ps
    case allLeft xs of
      Just ls -> unEL $ k ls
      Nothing -> undefined

instance Forward EL where
  afwd op = EL $ Call $ A $ Algebraic $ fmap unEL op
  sfwd op = EL $ Call $ S $ Enter $ fmap (fmap lift . unEL . fmap unEL) op
  lfwd op l st k = EL $ Call $ L $ Node op (EitherL (Right l)) (st' st) k'
   where
    st' st2 c l' = lift2 (fmap (\x -> EitherL <$> unEL (st2 c x)) (unEitherL l'))
    k' = lift . fmap (unEL . k) . unEitherL

instance Lift EitherL (Either Literal) where
  lift (Left x) = return (Left x)
  lift (Right x) = x
  lift2 (Left x) = return (EitherL $ Left x)
  lift2 (Right x) = x

maybeLeft :: Either a b -> Maybe a
maybeLeft = either Just (const Nothing)

allLeft :: [Either a b] -> Maybe [a]
allLeft = mapM maybeLeft

newtype EL sig sigs sigl l a = EL {unEL :: Prog (Sig sig sigs sigl (EitherL l)) (Either Literal a)}
  deriving (Functor)

instance (Functor sig, Functor sigs) => Pointed (EL sig sigs sigl l) where
  point = EL . return . Right

newtype EitherL l a = EitherL {unEitherL :: Either Literal (l a)}
  deriving (Show, Functor)

instance Pointed (EitherL Id) where
  point = EitherL . Right . point