module Types where
import Algebra (Modality)

type TypeVarName = String

type TypeName = String

arity :: Type -> Int
arity (_ :-> t) = 1 + arity t
arity _ = 0

retType :: Type -> Type
retType (_ :-> t) = retType t
retType t = t

data PrimType
    = IntegerType
    | CharType
    deriving (Eq, Ord, Show)

infixr 2 :->

data Type
    = (Modality, Type) :-> Type
    | PrimType PrimType
    | CustomType TypeName [Type]
    | TypeVar TypeVarName
    deriving (Eq, Show, Ord)
