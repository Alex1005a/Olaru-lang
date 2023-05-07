module Types where
import Algebra (Modality)
import GHC.Natural (Natural)

type TypeVar = Natural

type TypeName = String

arity :: Type -> Int
arity (_ :-> t) = 1 + arity t
arity _ = 0

retType :: Type -> Type
retType (_ :-> t) = retType t
retType t = t

funArgs :: Type -> [(Type, Modality)]
funArgs ((m, argTy) :-> retTy) = (argTy, m) : funArgs retTy
funArgs _ = []

data PrimType
    = IntegerType
    | CharType
    deriving (Eq, Ord, Show)

infixr 2 :->

data Type
    = (Modality, Type) :-> Type
    | PrimType PrimType
    | CustomType TypeName [Type]
    | TypeVar TypeVar
    deriving (Eq, Show, Ord)
