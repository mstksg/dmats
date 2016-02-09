{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE ExistentialQuantification #-}

module DMats.Types where

-- import Data.Singleton
-- import GHC.TypeLits
import Data.Type.Index
import Data.Type.Nat
import Data.Type.Product
import Data.Type.Sum
import Type.Class.Known
import Type.Family.List
import Type.Family.Nat
import Type.Family.Tuple      (Fst, Snd)
import qualified Data.Text    as T
import qualified GHC.TypeLits as TL

-- type family PrimReal (t :: Prim) :: * where
--     PrimReal PInt  = Int
--     PrimReal PBool = Bool

class HasEType t where
    type ToEType (t :: *) :: EType
    toExpr :: t -> Expr vs (ToEType t)

instance HasEType Int where
    type ToEType Int = TP PInt
    toExpr i = EO (OI i) Ø

instance HasEType Bool where
    type ToEType Bool = TSop '[Ø, Ø]
    toExpr False = EO (OCtr IZ)      (only (EO OProd Ø))
    toExpr True  = EO (OCtr (IS IZ)) (only (EO OProd Ø))

-- instance HasEType Bool where
--     type ToEType Bool = TSop '[Ø, Ø]
--     toExpr False = EO (OCtr IZ)      (only (EO OProd Ø))
--     toExpr True  = EO (OCtr (IS IZ)) (only (EO OProd Ø))

-- instance HasHType t where
--     type FromEType (t :: *) :: EType


data EType :: * where
    TUni  :: N         -> EType
    TP    :: Prim      -> EType
    (:->) :: EType     -> EType -> EType
    TSop  :: [[EType]] -> EType
    TSum  :: [EType]   -> EType
    TProd :: [EType]   -> EType
    -- TDecl :: [[EType]]  -> EType

data Prim = PInt
          | PString
          | PRVec TL.Nat -- this is a problem

type ExprList vs = Prod (Expr vs)

type ADT = Sum Tuple

-- sop: no recurisve types tho
-- and parameterized types can't work this way
type Unit        = TSop '[Ø]
type Bool'       = TSop '[Ø, Ø]
type Maybe' a    = TSop '[Ø, Only a]
type Either' a b = TSop '[Only a, Only b]

data Expr :: [EType] -> EType -> * where
    EV :: Index vs a       -> Expr vs a
    EU :: Nat n            -> Expr vs (TUni (S n))
    EO :: Op as a          -> ExprList vs as -> Expr vs a
    EΛ :: Expr (a :< vs) b -> Expr vs (a :-> b)
    EF :: (a -> Expr vs b) -> Expr vs (ToEType a) -> Expr vs b

data Op :: [EType] -> EType -> * where
    OT  :: EType  -> Op Ø (TUni n)
    OI  :: Int    -> Op Ø (TP PInt)
    OS  :: T.Text -> Op Ø (TP PString)
    ORV :: [Double] -> Op Ø (TP (PRVec n))

    OAp :: Op '[a :-> b, a] b

    -- OPlus   :: Op '[TP PInt, TP PInt] (TP PInt)
    -- OTimes  :: Op '[TP PInt, TP PInt] (TP PInt)
    -- ONegate :: Op '[TP PInt] (TP PInt)

    OSum  :: Op (TSum as :< (((:->) <$> as) <*> Only a)) a
    OInj  :: Index as a -> Op '[a] (TSum as)

    OProd :: Op as (TProd as)
    OProj :: Index as a -> Op '[TProd as] a

    OCase :: Op (TSop as :< (((:-> ) <$> (TProd <$> as)) <*> Only a)) a
    OCtr  :: Index as a -> Op '[TProd a] (TSop as)
    OAcc  :: Index as a -> Op '[TSop (Only as)] al

    -- OUnsafe :: (HasPrim t, ListC (SamePrim <$> Zip js ks)) => (Tuple js -> a) -> Op (TP <$> ks) (TP (ToPrim a))
    -- OUnsafe :: HasEType a => (a -> b) -> Op '[toEType a] (a)

depProd :: Expr vs (TP PInt :-> TUni n)
depProd = EΛ . flip EF (EV IZ) $ \i -> if even (i :: Int)
                                         then EO (OT (TP PInt)) Ø
                                         else EO (OT (TP PString)) Ø

-- depSum ::
