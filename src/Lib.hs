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
import Control.Applicative ((<|>))

someFunc :: IO ()
someFunc = putStrLn "someFunc"



data Query ext var   
    = Var var -- Constraint solver variables
    | Extrinsic ext -- Constant terms, defined outside of the core language.
    | Exists var (Query ext var)  -- Discharge a CSV
    | Apply (Query ext var) (Query ext var) -- Think about generalizing to (Apply (Query ext var) [Query ext var]). Do we want to allow CSVs to have function types?
    deriving (Show, Functor, Foldable, Traversable)

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
uniqify (Apply a b) = Apply <$> uniqify a <*> uniqify b







data ExampleJudgements var = ExampleJudgements {
        finite :: Bool, -- Should probably keep a proof here
        is :: Type var
    } deriving (Show, Functor)


data The x = The x


exampleJudge :: Judge ExampleJudgements ExampleExtrinsic
exampleJudge = Judge {jExtrinsic = jExtrinsic}
    where
    jExtrinsic judge_ gen = go
        where
        genWith judgement = do
            var <- gen
            () <- judge_ var judgement
            return var
        go (EInt _) = do
            tInt <- genWith $ ExampleJudgements {finite = True, is = TInt}
            tSet <- genWith $ ExampleJudgements {finite = True, is = (TSet tInt)} 
            return tSet
        go (EFloat _) = do
            tFloat <- genWith $ ExampleJudgements {finite = True, is = TFloat} 
            tSet <- genWith $ ExampleJudgements {finite = True, is = (TSet tFloat)} 
            return tSet
        go EMember = do
            tRet <- genWith $ ExampleJudgements {finite = True, is = TBool} 
            tSingleton <- gen -- TODO: Add ord constraint. Have to add constraints to type system first
            tSet <- genWith $ ExampleJudgements {finite = True, is = (TSet tSingleton)} 
            tAp1 <- genWith $ ExampleJudgements {finite = True, is = (TFun tSet tRet)}
            tAp2 <- genWith $ ExampleJudgements {finite = True, is = (TFun tSingleton tAp1)}
            return tAp2
    -- jIsFun arg ret = ExampleJudgements {finite = False, is =  (TFun arg ret)}

        -- with3 $ \a b c -> (j a b c, internals a b c, []) -- I need to think about this a bit more. I'm confusing myself with the 
        -- -- type of fully applying the function vs the type of the function itself. Do I need a separate type variable c at all?
        -- -- I think I definitely need to put a,b in the list. c might need special treatment? Or maybe a list is just the wrong structure.
        -- -- Maybe I really need  [data X = Z t | F t X]
        --     where
        --     j a b c = ExampleJudgements {finite = True, is = Just (TFun [a,b] c)} -- TODO: See if I can remove the Maybe now that I have tvars
        --     internals a b c = [(b, ExampleJudgements {finite = True, is = Just (TSet a)})
        --                       ,(c, ExampleJudgements {finite = True, is = Just TBool})]
    -- jApply tag = ExampleJ $ Except.throwError (Function tag)
    -- jRun :: forall a t v f . Applicative f => f v -> ExampleExtrinsic -> ExampleJ v t a -> f (Either (ErrorIn ExampleJudgements v t) (((ExampleJudgements v, [(v, ExampleJudgements v)])), a))
    -- jRun mkVar ext (ExampleJ e) = f <$> jExtrinsic mkVar ext
    --     where
    --     f = undefined -- This function needs to run the underlying StateT (keeping track of which arg to the function gets which judgements)
    --     -- I think maybe I don't need to actually return the list of judgements since judgeEach does that


data ExampleExtrinsic 
    = EInt [Int]
    | EFloat [Float]
    | EMember
    deriving Show

 
data ExampleTypeError var tag = UnificationFailure (Type var) (Type var) tag | NotFunction (Type var) tag deriving (Show, Functor)

data Type var 
    = TInt 
    | TFloat
    | TFun var var  -- arg, ret
    | TSet var 
    | TBool
    deriving (Eq, Ord, Show, Functor)



-- We need to make this monadic. It should check that the structure of x and y are the same, while emitting 
-- unifications of their variables.
unifyType :: Monad m => (var -> var -> m var') -> tag -> Type var -> Type var -> m (Either (ExampleTypeError var tag) (Type var'))
unifyType u t = go 
    where
    go TInt TInt = return (Right TInt)
    go TFloat TFloat = return (Right TFloat)
    go TBool TBool = return (Right TBool)
    go (TFun ix ox) (TFun iy oy) = Right <$> (TFun <$> u ix iy <*> u ox oy)
    go (TSet a) (TSet b) = Right . TSet <$> u a b
    go x y = return $ Left (UnificationFailure x y t)

applyType ::  Monad m => (var -> var -> m ()) -> tag -> Type var -> var -> m (Either (ExampleTypeError var tag) var)
applyType unify tag t1 arg = case t1 of
    TFun i o -> do
        unify i arg-- Pretty sure constructing an EJ here is wrong. Maybe I need two separate functions, for unifying cardinality and type? Or just add back the Nothing constructor of [is]?
        return $ Right o
    _ -> return $ Left (NotFunction t1 tag)

instance TypeSystem ExampleJudgements where
    type ErrorIn ExampleJudgements = ExampleTypeError
    topLevel = ExampleJudgements {finite = False, is = TBool}
    unifyOne u tag (ExampleJudgements f1 i1) (ExampleJudgements f2 i2) = fmap (fmap (ExampleJudgements (f1 || f2))) $ unifyType u tag i1 i2
    tApply judge_ tag (ExampleJudgements _f1 i1) i2 = applyType judge_ tag i1 i2 -- TODO: I need to figure out the correct way to propagate finitarity/membership info with apply. Will probably involve making a way to make finitarity judgements without also having an associated Type on hand?
    tIsFun i o = ExampleJudgements False (TFun i o)

data TCContext tvar var judgements = TCContext 
    { direct :: Map var tvar
    , judgements :: Map tvar judgements
    , freshTV :: tvar
    } deriving (Generic, Show)



emptyTCContext :: Enum tvar => TCContext tvar var judgements
emptyTCContext = TCContext Map.empty Map.empty (toEnum 0)

-- newtype TypecheckT 



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



class Functor judgements => TypeSystem judgements where
    type ErrorIn judgements :: * ->  * -> *
    -- Unify a single level of judgements. E.g. if you have [Set a] and [Set b], unify the [Set]s but outsource unifying a,b via the first arg
    unifyOne :: Monad m => (var -> var -> m var') -> tag -> judgements var -> judgements var -> m (Either (ErrorIn judgements var tag) (judgements var'))
    topLevel :: judgements var
    tApply :: Monad m => (var -> var -> m ()) -> tag -> judgements var -> var -> m (Either (ErrorIn judgements var tag) var)
    tIsFun :: var -> var -> judgements var
    -- applyT :: judgements var -> judgements var -> Either (ErrorIn


judgeVar :: (TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Ord var, Enum tvar) => var -> m tvar
judgeVar var = do
    associated <- Map.lookup var <$> CS.get @"direct"
    tvar <- case associated of 
        Just tvar -> return tvar
        Nothing -> do
            newTV <- mkFresh 
            CS.modify' @"direct" (Map.insert var newTV)
            return newTV
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
    

unifyVar :: forall tvar var judgements m . (TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Enum tvar) => tvar -> tvar -> m tvar
unifyVar a b = do
        new <- mkFresh
        -- let find :: tvar -> Map tvar (judgements tvar) -> m (judgements tvar)
        --     find var = maybe (CE.throw @"bug" $ Deleted var) return . Map.lookup var
        judgements <- CS.get @"judgements"
        maybe (return ()) (judge new) $ Map.lookup a judgements
        a `replacedBy` new 
        maybe (return ()) (judge new) $ Map.lookup b judgements
        b `replacedBy` new
        return new

replacedBy :: forall tvar var judgements m . (TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Enum tvar) => tvar -> tvar -> m ()
a `replacedBy` b = do
    let replace tv = if tv == a then b else tv
    CS.modify @"direct" (fmap replace)
    CS.modify @"judgements" (Map.delete a)
    CS.modify @"judgements" (fmap (fmap replace))


apply :: forall tvar var judgements m . (TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Enum tvar) => tvar -> tvar -> m tvar
apply fun arg = do
    funJudgements <- (Map.lookup fun <$> CS.get @"judgements") >>= \case
        Nothing -> tIsFun <$> mkFresh <*> mkFresh
        Just j -> return j
    result <- tApply (\a b -> () <$ unifyVar a b) fun funJudgements arg
    case result of
        Right resVar -> return resVar
        Left err -> CE.throw @"type" err



-- class Database system where
--     type Finite system :: * -- Finite terms (sets, maps, ranges)
--     type Function system :: * 
--     -- Instead of having a separate set of terms for propositional 
--     -- constraints at the query level (equality, less than, etc.) 
--     -- I guess we can just do everything with normal terms

-- How should we decide what terms are allowed at the top level? I guess just things that have type Bool?
-- Do we distinguish between vars and finites/extrinsic terms?


data Judge judgements extrinsic = Judge {
        jExtrinsic :: forall var f . Monad f => (var -> judgements var -> f ()) -> f var -> extrinsic -> f var -- I need to let them unify created vars (with concrete types only?). Eg with this I can do TSet a, but not TSet Int
        -- jIsFun :: forall var . var -> var -> judgements var,
        -- jTopLevel :: forall var . judgements var -- Used for top level statements (i.e. the root expression, as well as the RHS of forall/exists/etc.)
    }


-- TODO: Add a final unification step to concretize return type. Can use union-find
typecheck :: forall var judgements tvar m extrinsic . (Ord var, TypeSystem judgements, MonadTypecheck tvar var judgements m, Ord tvar, Enum tvar, Functor (ErrorIn judgements var)) => Judge judgements extrinsic -> Query extrinsic var -> m tvar
typecheck dredd query = do
        tlv <- go query
        judge tlv topLevel
        return tlv
    where
    go :: Query extrinsic var -> m tvar
    go (Var var) = judgeVar var
    go (Exists _var q) = do -- TODO: Use _var when calculating set membership/exclusion
        rhs <- go q
        judge rhs topLevel
        return rhs
    go (Extrinsic ext) = jExtrinsic dredd judge mkFresh ext
    go (Apply ext qs) = do
        -- retTy <- mkFresh
        funTy <- go ext
        argTy <- go qs
        apply funTy argTy
        -- applyT judge () funTy argTy >>= \case 
        --     Left err -> CE.throw @"type" err
        --     Right var -> return var
        -- judge funTy (jIsFun dredd argTy retTy)
        -- return retTy

    -- go (Apply ext qs) = 
    -- go (Exists var q) = judge var defaultJudgement >> go q
    -- go (And q1 q2) = go q1 >> go q2
type MonadTypecheck tvar var judgements m = 
    (HasState "direct" (Map var tvar) m,
     HasState "judgements" (Map tvar (judgements tvar)) m, 
     HasState "fresh" tvar m,
     HasThrow "type" (ErrorIn judgements tvar tvar) m,
     HasThrow "bug" (Bug tvar) m)

annotateWith :: (MonadTypecheck tvar var judgements m, Ord var, Ord tvar) => (var -> Maybe tvar -> Maybe (judgements tvar) -> annotated) -> var -> m annotated
annotateWith f var = do
    direct <- CS.get @"direct"
    judgements <- CS.get @"judgements"
    let tvar = Map.lookup var direct
        jm = flip Map.lookup judgements =<< tvar
    return $ f var tvar jm
            




{-

{0} -> TBool
{3} -> 
{4} -> TFun {7} {TFun {7} {TBool}}
{7} -> TSet {7}


-}

-- Takes all unifications to their logical conclusion
postprocess :: (MonadTypecheck tvar var judgements m, Ord tvar) => m ()
postprocess = undefined 

data ExampleAnnotated tvar var = ExampleAnnotated {anVar :: var, anTvar :: Maybe tvar,  anJudgement :: Maybe (ExampleJudgements tvar)}

instance (Show var, Show tvar) => Show (ExampleAnnotated tvar var) where
    show (ExampleAnnotated var tv judgement) = "(" ++ show var ++ " : " ++ tv' ++ " ~ " ++ judgment' ++ ")"
        where
        tv' = case tv of
            Nothing -> "?"
            Just tv_ -> show tv_
        judgment' = case judgement of
            Nothing -> "?"
            Just (ExampleJudgements _ is) -> show is

process :: Ord name => Query ExampleExtrinsic name -> (Query ExampleExtrinsic VarID, RenameState name VarID, Either (TypeCheckError TVarID (ExampleTypeError TVarID TVarID)) (TVarID, Query ExampleExtrinsic (ExampleAnnotated TVarID VarID)), TCContext TVarID VarID (ExampleJudgements TVarID))
process query = (renamed, renameState, typeResult, context)
    where
    (renamed, renameState) = runIdentity $ runRenameT (uniqify query) emptyRenameState
    theCheck = do 
        topLevelTvar <- typecheck exampleJudge renamed
        annotated <- traverse (annotateWith ExampleAnnotated) renamed
        return (topLevelTvar, annotated)
    (typeResult, context) = runIdentity $ runTypecheckT theCheck emptyTCContext




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