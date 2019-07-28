{-# LANGUAGE UndecidableInstances #-} -- I'm adding this because GHC isn't smart enough to see that reducing an RBT is terminating
module Lib where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
-- import qualified Data.Set as Set
-- import Data.Set (Set)
import qualified Control.Monad.State as State
import qualified Control.Monad.Except as Except
import           Capability.Accessors (Field, Lift, Rename)
import qualified Capability.State as CS
import qualified Capability.Reader as CR
import qualified Capability.Error as CE
import   Capability.State (HasState, MonadState)
import   Capability.Error (HasThrow, MonadError)
import   Capability.Reader (HasReader)
import GHC.Generics (Generic)
import Control.Monad.Identity (runIdentity)
import Control.Applicative ((<|>))

someFunc :: IO ()
someFunc = putStrLn "someFunc"



data Query ext var   
    = Var var -- Constraint solver variables
    | Extrinsic ext -- Constant terms, defined outside of the core language.
    | Exists var (Query ext var)  -- Discharge a CSV
    | Apply ext [Query ext var] -- Think about generalizing to (Apply (Query ext var) [Query ext var]). Do we want to allow CSVs to have function types?
    deriving Show

data RenameState old new = RenameState {
        free :: Map old new, -- Free variables
        bound :: Map old new, -- Bound variables 
        backwards :: Map new old, -- Backwards lookup, for error reporting
        freshNew :: new -- A source of fresh new variables
    } deriving (Generic, Show)

emptyRenameState :: Enum new => RenameState old new
emptyRenameState = RenameState Map.empty Map.empty Map.empty (toEnum 0)

newtype RenameT old new m a = RenameT {getRenameT :: State.StateT (RenameState old new) m a}
    deriving newtype (Functor, Applicative, Monad)
    deriving (HasState "free" (Map old new)) via (Field "free" () (MonadState (State.StateT (RenameState old new) m)))
    deriving (HasReader "bound" (Map old new)) via (CR.ReadStatePure (Field "bound" () (MonadState (State.StateT (RenameState old new) m))))
    deriving (HasState "backwards" (Map new old)) via (Field "backwards" () (MonadState (State.StateT (RenameState old new) m)))
    deriving (HasState "fresh" new) via (Rename "freshNew" (Field "freshNew" () (MonadState (State.StateT (RenameState old new) m))))


newtype VarID = VarID Int deriving (Eq, Ord, Enum)
instance Show VarID where
    show (VarID i) = "<" ++ show i ++ ">"
newtype TVarID = TVarID Int deriving (Eq, Ord, Enum)
instance Show TVarID where
    show (TVarID i) = "{" ++ show i ++ "}"

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

-- Causes all distinct variables to have unique names
rename :: (Enum new, Ord new, Ord old, HasState "fresh" new m, Ord old, HasReader "bound" (Map old new) m, HasState "free" (Map old new) m, HasState "backwards" (Map new old) m) => old -> m new 
rename old = do
    bounds <- CR.ask @"bound"
    frees <- CS.get @"free"
    -- Bound variables take precendence (this also takes care of shadowing)
    case Map.lookup old bounds <|> Map.lookup old frees of 
        Just known -> return known
        Nothing -> do
            new <- mkFresh
            CS.modify' @"free" (Map.insert old new)
            CS.modify' @"backwards" (Map.insert new old)
            return new


type MonadRename old new m = (HasState "fresh" new m, Ord old, HasReader "bound" (Map old new) m, HasState "free" (Map old new) m, HasState "backwards" (Map new old) m)

uniqify :: (Enum new, Ord new, Ord old, MonadRename old new m) => Query finite old -> m (Query finite new)
uniqify (Var var) = Var <$> rename var
uniqify (Extrinsic ext) = return (Extrinsic ext)
uniqify (Exists var q) = do
    (q', new) <- withName var (uniqify q)
    return (Exists new q')
uniqify (Apply ext qs) = Apply ext <$> traverse uniqify qs




data Type = TInt | TFloat
    deriving (Eq, Ord, Show)


data ExampleJudgements = ExampleJudgements {
        finite :: Bool, -- Should probably keep a proof here
        is :: Maybe Type
    } deriving Show


data The x = The x


newtype ExampleJ tag a = ExampleJ (Except.Except (ErrorIn ExampleJudgements tag) a)
    deriving newtype (Functor, Applicative, Monad)

exampleJudge :: Judge ExampleJ ExampleJudgements ExampleExtrinsic
exampleJudge = Judge {jDefault = jDefault, jExtrinsic = jExtrinsic, jApply = jApply, jRun = jRun}
    where
    jDefault = ExampleJudgements False Nothing
    jExtrinsic (EInt _) = ExampleJudgements {finite = True, is = Just TInt}
    jExtrinsic (EFloat _) = ExampleJudgements {finite = True, is = Just TFloat}
    jApply tag = ExampleJ $ Except.throwError (Function tag)
    jRun ext (ExampleJ e) = (jExtrinsic ext,) <$> Except.runExcept e


data ExampleExtrinsic 
    = EInt [Int]
    | EFloat [Float]
    deriving Show


exampleJudgements :: ExampleExtrinsic -> ExampleJudgements
exampleJudgements (EInt _) = ExampleJudgements True (Just TInt)
exampleJudgements (EFloat _) = ExampleJudgements True (Just TFloat)


data Judge j judgements extrinsic = Judge {
        jDefault :: judgements, 
        jExtrinsic :: extrinsic -> judgements,
        jApply :: forall tag . tag -> j tag judgements, -- Used to generate judgements over the list of things
        jRun :: forall a t . extrinsic -> j t a -> Either (ErrorIn judgements t) (judgements, a)
    }

data ExampleTypeError tag = UnificationFailure Type Type tag | Function tag deriving (Show, Functor)

unifyMaybe :: tag -> Maybe Type -> Maybe Type -> Either (ExampleTypeError tag) (Maybe Type)
unifyMaybe _ Nothing a = Right a
unifyMaybe _ (Just x) Nothing = Right (Just x)
unifyMaybe t (Just x) (Just y) = if x == y then Right (Just x) else Left (UnificationFailure x y t)

instance TypeSystem ExampleJudgements where
    type ErrorIn ExampleJudgements = ExampleTypeError
    unify tag (ExampleJudgements f1 i1) (ExampleJudgements f2 i2) = (ExampleJudgements (f1 || f2)) <$> unifyMaybe tag i1 i2

data TCContext tvar var judgements = TCContext 
    { direct :: Map var tvar
    , judgements :: Map tvar judgements
    , freshTV :: tvar
    } deriving (Generic, Show)

emptyTCContext :: Enum tvar => TCContext tvar var judgements
emptyTCContext = TCContext Map.empty Map.empty (toEnum 0)

-- newtype TypecheckT 

type MonadTypecheck tvar var judgements m = 
    (HasState "direct" (Map var tvar) m,
     HasState "judgements" (Map tvar judgements) m, 
     HasState "fresh" tvar m,
     HasThrow "type" (ErrorIn judgements tvar) m)


newtype TypecheckT tvar var judgements err m a = TypecheckT {getTypecheckT :: Except.ExceptT err (State.StateT (TCContext tvar var judgements) m) a}
    deriving newtype (Functor, Applicative, Monad)
    deriving (HasState "direct" (Map var tvar)) via ((Lift (Except.ExceptT err (Field "direct" () (MonadState (State.StateT (TCContext tvar var judgements) m))))))
    deriving (HasState "judgements" (Map tvar judgements)) via ((Lift (Except.ExceptT err (Field "judgements" () (MonadState (State.StateT (TCContext tvar var judgements) m))))))
    deriving (HasState "fresh" tvar) via ((Lift (Except.ExceptT err (Rename "freshTV" (Field "freshTV" () (MonadState (State.StateT (TCContext tvar var judgements) m)))))))
    deriving (HasThrow "type" err) via (MonadError (Except.ExceptT err (State.StateT (TCContext tvar var judgements) m)))


runTypecheckT :: TypecheckT tvar var judgements err m a -> TCContext tvar var judgements -> m (Either err a, TCContext tvar var judgements)
runTypecheckT (TypecheckT tc) = State.runStateT (Except.runExceptT tc) 

class TypeSystem judgements where
    type ErrorIn judgements :: * -> *
    unify :: tag -> judgements -> judgements -> Either (ErrorIn judgements tag) judgements


judgeVar :: (TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Ord var, Enum tvar) => var -> judgements -> m tvar
judgeVar var newJudgements = do
    associated <- Map.lookup var <$> CS.get @"direct"
    tvar <- case associated of 
        Just tvar -> return tvar
        Nothing -> do
            newTV <- mkFresh 
            CS.modify' @"direct" (Map.insert var newTV)
            return newTV
    judge tvar newJudgements
    return tvar


judge :: (TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar) => tvar -> judgements -> m ()
judge tvar newJudgements = do
    judgements <- Map.lookup tvar <$> CS.get @"judgements"
    case judgements of
        Nothing -> CS.modify' @"judgements" (Map.insert tvar newJudgements)
        Just preexisting -> case unify tvar preexisting newJudgements of
            Right consistent -> CS.modify' @"judgements" (Map.insert tvar consistent)
            Left err -> CE.throw @"type" err


-- class Database system where
--     type Finite system :: * -- Finite terms (sets, maps, ranges)
--     type Function system :: * 
--     -- Instead of having a separate set of terms for propositional 
--     -- constraints at the query level (equality, less than, etc.) 
--     -- I guess we can just do everything with normal terms

-- How should we decide what terms are allowed at the top level? I guess just things that have type Bool?
-- Do we distinguish between vars and finites/extrinsic terms?



typecheck :: forall var judgements tvar j m extrinsic . (Ord var, TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Enum tvar, (forall tag . Monad (j tag)), Functor (ErrorIn judgements)) => Judge j judgements extrinsic -> Query extrinsic var -> m tvar
typecheck dredd = go
    where
    go (Var var) = judgeVar var (jDefault dredd)
    go (Exists var q) = judgeVar var (jDefault dredd) >> go q
    go (Extrinsic ext) = do
        extVar <- mkFresh
        judge extVar $ jExtrinsic dredd ext
        return extVar
    go (Apply ext qs) = do
        appliedType <- mkFresh
        tvars <- traverse go qs -- Type all arguments
        let judgeEach :: tvar -> j tvar (m ())
            judgeEach argVar = do 
                judgement <- jApply dredd argVar
                return (judge argVar judgement)
        (appliedJudgement, subjudgements) <- either (CE.throw @"type") return $ jRun dredd ext (traverse judgeEach tvars)
        sequence_ subjudgements
        judge appliedType appliedJudgement
        return appliedType

    -- go (Apply ext qs) = 
    -- go (Exists var q) = judge var defaultJudgement >> go q
    -- go (And q1 q2) = go q1 >> go q2




process :: Ord name => Query ExampleExtrinsic name -> (Query ExampleExtrinsic VarID, RenameState name VarID, Either (ExampleTypeError TVarID) TVarID, TCContext TVarID VarID ExampleJudgements)
process query = (renamed, renameState, typeResult, context)
    where
    (renamed, renameState) = runIdentity $ runRenameT (uniqify query) emptyRenameState
    (typeResult, context) = runIdentity $ runTypecheckT (typecheck exampleJudge renamed) emptyTCContext




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