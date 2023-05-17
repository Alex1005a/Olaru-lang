module Algebra where

data Modality
    = Unrestricted
    | Relevant
    | Affine
    | Linear
    | Ordered
    | Zero
    deriving (Eq, Show, Ord)

more :: Modality -> Modality -> Bool
more Zero _ = True
more Linear Affine = True
more Linear Relevant = True
more _ Unrestricted = True
more ts1 ts2 = ts1 == ts2

mult :: Modality -> Modality -> Modality
mult Ordered _ = Ordered
mult _ Ordered = Ordered
mult Linear ts = ts
mult ts Linear = ts
mult Unrestricted _ = Unrestricted
mult _ Unrestricted = Unrestricted
mult Affine Affine = Affine
mult Relevant Relevant = Relevant
mult Relevant Affine = Unrestricted
mult Affine Relevant = Unrestricted
mult Zero _ = Zero
mult _ Zero = Zero