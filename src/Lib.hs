{-# LANGUAGE UndecidableInstances #-} -- I'm adding this because GHC isn't smart enough to see that reducing an RBT is terminating
module Lib where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
-- import qualified Data.Set as Set
-- import Data.Set (Set)
import qualified Control.Monad.State as State
import qualified Control.Monad.Except as Except
import           Capability.Accessors (Field, Lift, Rename, Ctor)
import qualified Capability.State as CS
import qualified Capability.Reader as CR
import qualified Capability.Error as CE
import   Capability.State (HasState, MonadState)
import   Capability.Error (HasThrow, MonadError)
import   Capability.Reader (HasReader)
import GHC.Generics (Generic)
import Control.Monad.Identity (runIdentity)
import Control.Monad (zipWithM)
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







data ExampleJudgements var = ExampleJudgements {
        finite :: Bool, -- Should probably keep a proof here
        is :: Maybe (Type var)
    } deriving Show


data The x = The x


newtype ExampleJ var tag a = ExampleJ (State.StateT [var] (Except.Except (ErrorIn ExampleJudgements var tag)) a)
    deriving newtype (Functor, Applicative, Monad)

exampleJudge :: Judge ExampleJ ExampleJudgements ExampleExtrinsic
exampleJudge = Judge {jDefault = jDefault, jExtrinsic = jExtrinsic, jApply = jApply, jRun = jRun}
    where
    jDefault = ExampleJudgements False Nothing
    jExtrinsic gen ext = fmap (\(rootJudgement, internalJudgements, _funVars) -> (rootJudgement, internalJudgements)) (jExtrinsic' gen ext )
    jExtrinsic' gen = go
        where
        with f = f <$> gen
        with3 f = f <$> gen <*> gen <*> gen
        go (EInt _) = with $ \a -> (j a, [internal a], [])
            where
            j a = ExampleJudgements {finite = True, is = Just (TSet a)} 
            internal a = (a, ExampleJudgements {finite = True, is = Just TInt})
        go (EFloat _) = with $ \a -> (j a, [internal a], [])
            where
            j a = ExampleJudgements {finite = True, is = Just (TSet a)} 
            internal a = (a, ExampleJudgements {finite = True, is = Just TFloat})
        go EMember = with3 $ \a b c -> (j a b c, internals a b c, []) -- I need to think about this a bit more. I'm confusing myself with the 
        -- type of fully applying the function vs the type of the function itself. Do I need a separate type variable c at all?
        -- I think I definitely need to put a,b in the list. c might need special treatment? Or maybe a list is just the wrong structure.
        -- Maybe I really need  [data X = Z t | F t X]
            where
            j a b c = ExampleJudgements {finite = True, is = Just (TFun [a,b] c)} -- TODO: See if I can remove the Maybe now that I have tvars
            internals a b c = [(b, ExampleJudgements {finite = True, is = Just (TSet a)})
                              ,(c, ExampleJudgements {finite = True, is = Just TBool})]
    jApply tag = ExampleJ $ Except.throwError (Function tag)
    jRun :: forall a t v f . Applicative f => f v -> ExampleExtrinsic -> ExampleJ v t a -> f (Either (ErrorIn ExampleJudgements v t) (((ExampleJudgements v, [(v, ExampleJudgements v)])), a))
    jRun mkVar ext (ExampleJ e) = f <$> jExtrinsic mkVar ext
        where
        f = undefined -- This function needs to run the underlying StateT (keeping track of which arg to the function gets which judgements)
        -- I think maybe I don't need to actually return the list of judgements since judgeEach does that


data ExampleExtrinsic 
    = EInt [Int]
    | EFloat [Float]
    | EMember
    deriving Show

data Judge j judgements extrinsic = Judge {
        jDefault :: forall var . judgements var, 
        jExtrinsic :: forall var f . Applicative f => f var -> extrinsic -> f (judgements var, [(var, judgements var)]), -- I need to let them unify created vars (with concrete types only?). Eg with this I can do TSet a, but not TSet Int
        jApply :: forall tag var . tag -> j var tag (judgements var), -- Used to generate judgements over the list of things
        jRun :: forall a tag var f . Applicative f => f var -> extrinsic -> j var tag a -> f (Either (ErrorIn judgements var tag) ((judgements var, [(var, judgements var)]), a))
    }

data ExampleTypeError var tag = UnificationFailure (Type var) (Type var) tag | Function tag deriving (Show, Functor)

data Type var = TInt | TFloat | TFun [var] var | TSet var | TBool
    deriving (Eq, Ord, Show)

-- We need to make this monadic. It should check that the structure of x and y are the same, while emitting 
-- unifications of their variables.
unifyMaybe :: Monad m => (var -> var -> m var) -> tag -> Maybe (Type var) -> Maybe (Type var) -> m (Either (ExampleTypeError var tag) (Maybe (Type var)))
unifyMaybe u t = loop 
    where
    loop Nothing a = return (Right a)
    loop (Just x) Nothing = return (Right (Just x))
    loop (Just x) (Just y) = go x y 
    go TInt TInt = return (Right (Just TInt))
    go TFloat TFloat = return (Right (Just TFloat))
    go (TFun xs x) (TFun ys y) | length xs == length ys = Right . Just  <$> (TFun <$> zipWithM u xs ys <*> u x y)
    go x y = return $ Left (UnificationFailure x y t)

instance TypeSystem ExampleJudgements where
    type ErrorIn ExampleJudgements = ExampleTypeError
    unifyOne u tag (ExampleJudgements f1 i1) (ExampleJudgements f2 i2) = fmap (fmap (ExampleJudgements (f1 || f2))) $ unifyMaybe u tag i1 i2

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
     HasState "judgements" (Map tvar (judgements tvar)) m, 
     HasState "fresh" tvar m,
     HasThrow "type" (ErrorIn judgements tvar tvar) m,
     HasThrow "bug" (Bug tvar) m)

data Bug tvar = Deleted tvar deriving Show

data TypeCheckError tvar err = Bug (Bug tvar) | Unification err deriving (Generic, Show)

newtype TypecheckT tvar var judgements err m a = TypecheckT {getTypecheckT :: Except.ExceptT (TypeCheckError tvar err) (State.StateT (TCContext tvar var judgements) m) a}
    deriving newtype (Functor, Applicative, Monad)
    deriving (HasState "direct" (Map var tvar)) via ((Lift (Except.ExceptT (TypeCheckError tvar err) (Field "direct" () (MonadState (State.StateT (TCContext tvar var judgements) m))))))
    deriving (HasState "judgements" (Map tvar judgements)) via ((Lift (Except.ExceptT (TypeCheckError tvar err) (Field "judgements" () (MonadState (State.StateT (TCContext tvar var judgements) m))))))
    deriving (HasState "fresh" tvar) via ((Lift (Except.ExceptT (TypeCheckError tvar err) (Rename "freshTV" (Field "freshTV" () (MonadState (State.StateT (TCContext tvar var judgements) m)))))))
    deriving (HasThrow "type" err) via (Rename "Unification" (Ctor "Unification"  () (MonadError (Except.ExceptT (TypeCheckError tvar err) (State.StateT (TCContext tvar var judgements) m)))))
    deriving (HasThrow "bug" (Bug tvar)) via (Rename "Bug" (Ctor "Bug"  () (MonadError (Except.ExceptT (TypeCheckError tvar err) (State.StateT (TCContext tvar var judgements) m)))))


runTypecheckT :: TypecheckT tvar var judgements err m a -> TCContext tvar var judgements -> m (Either (TypeCheckError tvar err) a, TCContext tvar var judgements)
runTypecheckT (TypecheckT tc) = State.runStateT (Except.runExceptT tc) 

class TypeSystem judgements where
    type ErrorIn judgements :: * ->  * -> *
    -- Unify a single level of judgements. E.g. if you have [Set a] and [Set b], unify the [Set]s but outsource unifying a,b via the first arg
    unifyOne :: Monad m => (var -> var -> m var) -> tag -> judgements var -> judgements var -> m (Either (ErrorIn judgements var tag) (judgements var))


judgeVar :: (TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Ord var, Enum tvar) => var -> judgements tvar -> m tvar
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


judge :: forall tvar var judgements m . (TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Enum tvar) => tvar -> judgements tvar -> m ()
judge tvar newJudgements = do
    judgements <- Map.lookup tvar <$> CS.get @"judgements"
    case judgements of
        Nothing -> CS.modify' @"judgements" (Map.insert tvar newJudgements)
        Just preexisting -> do
            unified <- unifyOne unifyVar tvar preexisting newJudgements 
            case unified of
                Right consistent -> CS.modify' @"judgements" (Map.insert tvar consistent)
                Left err -> CE.throw @"type" err
    where
    replacedBy :: tvar -> tvar -> m ()
    a `replacedBy` b = do
        CS.modify @"direct" (fmap (\tv -> if tv == a then b else tv))
        CS.modify @"judgements" (Map.delete a)
    unifyVar :: tvar -> tvar -> m tvar
    unifyVar a b = do
        new <- mkFresh
        let find :: tvar -> Map tvar (judgements tvar) -> m (judgements tvar)
            find var = maybe (CE.throw @"bug" $ Deleted var) return . Map.lookup var
        ja <- find a =<< CS.get @"judgements"
        jb <- find b =<< CS.get @"judgements"
        judge new ja 
        judge new jb
        a `replacedBy` new 
        b `replacedBy` new
        return new




-- class Database system where
--     type Finite system :: * -- Finite terms (sets, maps, ranges)
--     type Function system :: * 
--     -- Instead of having a separate set of terms for propositional 
--     -- constraints at the query level (equality, less than, etc.) 
--     -- I guess we can just do everything with normal terms

-- How should we decide what terms are allowed at the top level? I guess just things that have type Bool?
-- Do we distinguish between vars and finites/extrinsic terms?



typecheck :: forall var judgements tvar j m extrinsic . (Ord var, TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Enum tvar, (forall tag var . Monad (j var tag)), Functor (ErrorIn judgements var)) => Judge j judgements extrinsic -> Query extrinsic var -> m tvar
typecheck dredd = go
    where
    go :: Query extrinsic var -> m tvar
    go (Var var) = judgeVar var (jDefault dredd)
    go (Exists var q) = judgeVar var (jDefault dredd) >> go q
    go (Extrinsic ext) = do
        extVar <- mkFresh :: m tvar
        (judgement, internalUnifications) <- jExtrinsic dredd mkFresh ext
        mapM_ (uncurry judge) internalUnifications
        judge extVar judgement 
        return extVar
    go (Apply ext qs) = do
        appliedType <- mkFresh
        tvars <- traverse go qs -- Type all arguments
        let judgeEach :: tvar -> j tvar tvar (m ())
            judgeEach argVar = do 
                judgement <- jApply dredd argVar
                return (judge argVar judgement)
        judgeExtResult <- jRun dredd mkFresh ext (traverse judgeEach tvars)
        ((appliedRootJudgement, appliedInternalJudgements), subjudgements) <- either (CE.throw @"type") return judgeExtResult
        sequence_ subjudgements
        judge appliedType appliedRootJudgement
        mapM_ (uncurry judge) appliedInternalJudgements
        return appliedType

    -- go (Apply ext qs) = 
    -- go (Exists var q) = judge var defaultJudgement >> go q
    -- go (And q1 q2) = go q1 >> go q2




process :: Ord name => Query ExampleExtrinsic name -> (Query ExampleExtrinsic VarID, RenameState name VarID, Either (TypeCheckError TVarID (ExampleTypeError TVarID TVarID)) TVarID, TCContext TVarID VarID (ExampleJudgements TVarID))
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