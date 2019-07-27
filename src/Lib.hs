{-# LANGUAGE UndecidableInstances #-} -- I'm adding this because GHC isn't smart enough to see that reducing an RBT is terminating
module Lib where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
-- import qualified Data.Set as Set
-- import Data.Set (Set)
import qualified Control.Monad.State as State
import qualified Control.Monad.Except as Except
import           Capability.Accessors (Field, Lift)
import qualified Capability.State as CS
import qualified Capability.Reader as CR
import qualified Capability.Error as CE
import   Capability.State (HasState, MonadState)
import   Capability.Error (HasThrow, MonadError)
import   Capability.Reader (HasReader)
import GHC.Generics (Generic)
import Control.Monad.Identity (runIdentity)

someFunc :: IO ()
someFunc = putStrLn "someFunc"



data Query finite var   
    = Member var finite
    | Exists var (Query finite var)
    | And (Query finite var) (Query finite var)
    deriving Show

data RenameState old new = RenameState {
        free :: Map old new, -- Free variables
        bound :: Map old new, -- Bound variables 
        backwards :: Map new old, -- Backwards lookup, for error reporting
        fresh :: new -- A source of fresh new variables
    } deriving (Generic, Show)

emptyRenameState :: Enum new => RenameState old new
emptyRenameState = RenameState Map.empty Map.empty Map.empty (toEnum 0)

newtype RenameT old new m a = RenameT {getRenameT :: State.StateT (RenameState old new) m a}
    deriving newtype (Functor, Applicative, Monad)
    deriving (HasState "free" (Map old new)) via (Field "free" () (MonadState (State.StateT (RenameState old new) m)))
    deriving (HasReader "bound" (Map old new)) via (CR.ReadStatePure (Field "bound" () (MonadState (State.StateT (RenameState old new) m))))
    deriving (HasState "backwards" (Map new old)) via (Field "backwards" () (MonadState (State.StateT (RenameState old new) m)))
    deriving (HasState "fresh" new) via (Field "fresh" () (MonadState (State.StateT (RenameState old new) m)))


newtype VarID = VarID Int deriving (Eq, Ord, Enum)
instance Show VarID where
    show (VarID i) = "<" ++ show i ++ ">"


runRenameT :: RenameT old new m a -> RenameState old new -> m (a, RenameState old new)
runRenameT = State.runStateT . getRenameT

mkFresh :: (Enum t, HasState "fresh" t m) => m t
mkFresh = CS.get @"fresh" <* CS.modify' @"fresh" succ


withName :: (Monad m, Enum new, HasState "fresh" new m, Ord new, Ord old, HasState "backwards" (Map new old) m, HasReader "bound" (Map old new) m) => old -> m a -> m (a, new) 
withName old x = do
    new <- mkFresh
    result <- CR.local @"bound" (Map.insert old new) x
    CS.modify' @"backwards" (Map.insert new old)
    return (result, new)

rename :: (Enum new, Ord new, Ord old, HasState "fresh" new m, Ord old, HasReader "bound" (Map old new) m, HasState "free" (Map old new) m, HasState "backwards" (Map new old) m) => old -> m new 
rename old = do
    bounds <- CR.ask @"bound"
    case Map.lookup old bounds of 
        Just bound -> return bound
        Nothing -> do
            frees <- CS.get @"free"
            case Map.lookup old frees of
                Just free -> return free
                Nothing -> do
                    free <- mkFresh
                    CS.modify' @"free" (Map.insert old free)
                    CS.modify' @"backwards" (Map.insert free old)
                    return free


type MonadRename old new m = (HasState "fresh" new m, Ord old, HasReader "bound" (Map old new) m, HasState "free" (Map old new) m, HasState "backwards" (Map new old) m)

uniqify :: (Enum new, Ord new, Ord old, MonadRename old new m) => Query finite old -> m (Query finite new)
uniqify (Member var finite) = (`Member` finite) <$> rename var
uniqify (Exists var q) = do
    (q', new) <- withName var (uniqify q)
    return (Exists new q')
uniqify (And q1 q2) = And <$> uniqify q1 <*> uniqify q2






data Type = TInt | TFloat
    deriving (Eq, Ord, Show)


data Judgements = Judgements {
        finite :: Bool, -- Should probably keep a proof here
        is :: Maybe Type
    } deriving Show

defaultJudgements :: Judgements
defaultJudgements = Judgements False Nothing

data TypeError tag = UnificationFailure Type Type tag deriving Show

unifyMaybe :: tag -> Maybe Type -> Maybe Type -> Either (TypeError tag) (Maybe Type)
unifyMaybe _ Nothing a = Right a
unifyMaybe _ (Just x) Nothing = Right (Just x)
unifyMaybe t (Just x) (Just y) = if x == y then Right (Just x) else Left (UnificationFailure x y t)

instance TypeSystem Judgements where
    type ErrorIn Judgements = TypeError
    unify tag (Judgements f1 i1) (Judgements f2 i2) = (Judgements (f1 || f2)) <$> unifyMaybe tag i1 i2

data TCContext var judgements = TCContext 
    { judgements :: Map var judgements
    } deriving (Generic, Show)

emptyTCContext :: TCContext var judgements
emptyTCContext = TCContext Map.empty

-- newtype TypecheckT 

type MonadTypecheck var judgements m = 
    (HasState "judgements" (Map var judgements) m, 
     HasThrow "type" (ErrorIn judgements var) m)


newtype TypecheckT var judgements err m a = TypecheckT {getTypecheckT :: Except.ExceptT err (State.StateT (TCContext var judgements) m) a}
    deriving newtype (Functor, Applicative, Monad)
    deriving (HasState "judgements" (Map var judgements)) via ((Lift (Except.ExceptT err (Field "judgements" () (MonadState (State.StateT (TCContext var judgements) m))))))
    deriving (HasThrow "type" err) via (MonadError (Except.ExceptT err (State.StateT (TCContext var judgements) m)))


runTypecheckT :: TypecheckT var judgements err m a -> TCContext var judgements -> m (Either err a, TCContext var judgements)
runTypecheckT (TypecheckT tc) = State.runStateT (Except.runExceptT tc) 

class TypeSystem judgements where
    type ErrorIn judgements :: * -> *
    unify :: tag -> judgements -> judgements -> Either (ErrorIn judgements tag) judgements

judge :: (TypeSystem judgements, MonadTypecheck var judgements m, Ord var) => var -> judgements -> m ()
judge var newJudgements = do
    judgements <- Map.lookup var <$> CS.get @"judgements"
    case judgements of
        Nothing -> CS.modify' @"judgements" (Map.insert var newJudgements)
        Just preexisting -> case unify var preexisting newJudgements of
            Right consistent -> CS.modify' @"judgements" (Map.insert var consistent)
            Left err -> CE.throw @"type" err


typecheck :: (Ord var, TypeSystem judgements, MonadTypecheck var judgements m) => judgements -> (finite -> judgements) -> Query finite var -> m ()
typecheck defaultJudgement inferredFrom = go
    where
    go (Member var finite) = judge var (inferredFrom finite)
    go (Exists var q) = judge var defaultJudgement >> go q
    go (And q1 q2) = go q1 >> go q2


data ExampleFinite 
    = EInt [Int]
    | EFloat [Float]
    deriving Show


exampleJudgements :: ExampleFinite -> Judgements
exampleJudgements (EInt _) = Judgements True (Just TInt)
exampleJudgements (EFloat _) = Judgements True (Just TFloat)



process :: Ord name => Query ExampleFinite name -> (Query ExampleFinite VarID, RenameState name VarID, Either (TypeError VarID) (), TCContext VarID Judgements)
process query = (renamed, renameState, typeResult, context)
    where
    (renamed, renameState) = runIdentity $ runRenameT (uniqify query) emptyRenameState
    (typeResult, context) = runIdentity $ runTypecheckT (typecheck defaultJudgements exampleJudgements renamed) emptyTCContext



-- uniqify (


-- fresh :: 

-- Checks that A) types unify and are constrained and B) types are finite
-- typecheck :: Monad m => Query finite var tyvar -> CheckT finite m (Query finite var Type)
-- typecheck = undefined

-- rename :: Monad m => Query finite Text tyvar -> FreshT Int m (Query finite Int tyvar, Map Int Text)
-- rename = undefined
--     go :: Map Text Int -> Query finite Text tyvar -> FreshT Int m (Query finite Int tyvar, Map Int Text)
--     go activeRenames = \case 
--         M

-- typecheck' :: (Monad m, Enum tyvar, Ord tyvar, Ord var) => Query finite var tyvar -> CheckT tyvar m (QContext var tyvar)
-- typecheck' (Member var finite) = do
--     tyvar <- fresh
--     return $
--         QContext {finite = Map.singleton var tyvar
--                  ,infinite = Map.empty 
--                  ,judgements = Map.singleton tyvar Set.empty}
-- typecheck' (




-- import Data.RBR (Map, Empty, Record, I(..), Delete, KeysValuesAll, PresentIn, Insert, FromList, Value, toRecord, insert, unit, delete)
-- import Data.RBR.Internal(Map(N, E))
-- import GHC.TypeLits (Symbol)
-- import Data.Kind (Type, Constraint)
-- import Data.Type.Bool (If)
-- import Data.Type.Equality (type (==))

-- data sym :- ty = Var


-- -- type family Intersection
-- type family Union (a :: Map Symbol Type) (b :: Map Symbol Type) where
--     Union Empty b = b
--     Union (N _color left k2 v2 right) b = Insert k2 v2 (Union left (Union right b)) 

-- type family Subtract (a :: Map Symbol Type) (b :: Map Symbol Type) where
--     Subtract a Empty = a
--     Subtract a (N _color left k2 v2 right) = Delete k2 v2 (Subtract (Subtract a right) left)

-- -- type Union a b c = (KeysValuesAll (PresentIn c) a, KeysValuesAll (PresentIn c) b)

-- -- class (Delete k v map ~ map) => NotIn map k v  where

-- -- type Subtract a b c = (KeysValuesAll (NotIn b) c, Union a b c)


-- data FiniteSet t = FiniteSet [t]


-- data Query (finite :: Map Symbol Type) (infinite :: Map Symbol Type) where
--     Member :: existential :- t -> FiniteSet t -> Query (FromList '[ '(existential, t)]) E
--     Exists :: (Value existential finite ~ t) => existential :- t -> Query finite infinite -> Query (Delete existential t finite) infinite
--     Join :: Query fin1 inf1 -> Query fin2 inf2 -> Query (Union fin1 fin2) ((Union inf1 inf2) `Subtract` (Union fin1 fin2))
--     -- Member :: 


-- x = Member (Var :: "foo" :- Int) (FiniteSet [1,2,3])

-- y = Exists (Var :: "foo" :- Int) x


-- a = Member (Var :: "bar" :- Float) (FiniteSet [1,2,3])

-- b = Exists (Var :: "bar" :- Float) a


-- xa = Join x a

-- yb = Join y b

-- yb_1 = Exists (Var :: "foo" :- Int) xa
-- yb_2 = Exists (Var :: "bar" :- Float) yb_1

-- -- Not to be taken literally
-- evaluate :: Query finite Empty -> [Record I finite]
-- evaluate (Member Var (FiniteSet ls)) = map (\l -> insert (I l) unit) ls
-- -- evaluate (Join as bs) = do
-- --     as <- evaluate as
-- --     bs <- evaluate bs
-- --     _ as bs

-- given :: 

-- -- evaluate (Exists (Var :: existential :- t) query) = map (delete @existential) $ evaluate query


-- x_res = evaluate x