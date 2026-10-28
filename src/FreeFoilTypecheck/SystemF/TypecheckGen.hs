{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FunctionalDependencies #-}

module FreeFoilTypecheck.SystemF.TypecheckGen
  ( Context(..)
  , MonadScopedReader(..)
  , MonadContext
  , AlphaEquiv(..)
  , TypingSig(..)
  , defaultCheckSig
  , TypedPattern(..)
  , bidirectionalCheck
  , bidirectionalInfer
  , Scoped(..)
  , mapBinder, mapScoped
  , TypeError(..)
  , TypedNameBinders(..)
  , TypedAST(..), toAST
  , ScopedTypedAST
  , typeOf
  , CheckInfer(..)
  , ScopedCheckInfer
  , ScopedCheckInfer'(..)
  , shouldBe
  , substituteInContext
  , withBoundType
  ) where

import Control.Monad (unless)
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.Foil hiding (AlphaEquiv)
import Control.Monad.Foil.Relative
import Control.Monad.Free.Foil hiding (alphaEquiv)
import Control.Monad.Free.Foil qualified as FreeFoil (alphaEquiv)
import Data.Bifunctor (bimap, Bifunctor)
import Data.Bitraversable (Bitraversable)
import Data.Kind (Type, Constraint)
import Data.ZipMatchK (ZipMatchK)

-- | Main typing signature class
type TypingSig :: (S -> S -> Type) -> (S -> Type) -> (Type -> Type -> Type) -> (S -> Type -> Type) -> Constraint
class
  (forall n. Show (TypeError (ty n)), AlphaEquiv ty, MonadContext ty m) =>
  TypingSig binder ty sig m
  where
  checkSig ::
    (Distinct n) =>
    sig (ScopedCheckInfer binder sig ty m n) (CheckInfer binder sig ty m n) ->
    ty n ->
    m n (TypedAST binder sig ty n)

  default checkSig ::
    (MonadError String (m n), Distinct n) =>
    sig (ScopedCheckInfer binder sig ty m n) (CheckInfer binder sig ty m n) ->
    ty n ->
    m n (TypedAST binder sig ty n)
  checkSig = defaultCheckSig

  inferSig ::
    (Distinct n) =>
    sig (ScopedCheckInfer binder sig ty m n) (CheckInfer binder sig ty m n) ->
    m n (TypedAST binder sig ty n)

defaultCheckSig ::
  (TypingSig binder ty sig m, MonadError String (m n), Distinct n, MonadContext ty m) =>
  sig (ScopedCheckInfer binder sig ty m n) (CheckInfer binder sig ty m n) ->
  ty n ->
  m n (TypedAST binder sig ty n)
defaultCheckSig node expectedType = do
  typedNode <- inferSig node
  nodeTy <- typeOf typedNode
  typesAreAlphaEquiv <- alphaEquivInContext nodeTy expectedType
  unless typesAreAlphaEquiv do
    throwError (show (TypeErrorUnexpectedType nodeTy expectedType))
  pure typedNode

bidirectionalInfer ::
  forall ty binder sig m n.
  ( Distinct n,
    Bifunctor sig,
    AlphaEquiv ty,
    TypingSig binder ty sig m,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder,
    forall x. MonadError String (m x),
    MonadContext ty m
  ) =>
  AST binder sig n ->
  m n (TypedAST binder sig ty n)
bidirectionalInfer t = infer $ bidirectionalCheckInfer t

bidirectionalCheck ::
  forall ty binder sig m n.
  ( Distinct n,
    Bifunctor sig,
    AlphaEquiv ty,
    TypingSig binder ty sig m,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder,
    forall x. MonadError String (m x),
    MonadContext ty m
  ) =>
  AST binder sig n ->
  ty n -> m n (TypedAST binder sig ty n)
bidirectionalCheck t = check $ bidirectionalCheckInfer t

lookupNameInContext :: MonadContext ty m => Name n -> m n (ty n)
lookupNameInContext name = lookupName name . unContext <$> askScoped

alphaEquivInContext :: (MonadContext ty m, AlphaEquiv ty, Distinct n) => ty n -> ty n -> m n Bool
alphaEquivInContext x y = do
  Context nameMap <- askScoped
  pure $ alphaEquiv (nameMapToScope nameMap) x y

substituteInContext
  :: (MonadContext ty m, Bifunctor sig, Distinct n, CoSinkable binder, SinkableK binder)
  => Substitution (AST binder sig) i n -> AST binder sig i
  -> m n (AST binder sig n)
substituteInContext subst ty = do
  Context nameMap <- askScoped
  pure $ substitute (nameMapToScope nameMap) subst ty

bidirectionalCheckInfer ::
  forall ty binder sig m n.
  ( Distinct n,
    Bifunctor sig,
    TypingSig binder ty sig m,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder,
    forall x. MonadError String (m x),
    MonadContext ty m
  ) =>
  AST binder sig n ->
  CheckInfer binder sig ty m n
bidirectionalCheckInfer = \case
  Var n -> do
    CheckInfer
      { infer = do
          pure $ TypedVar n
      , check = \expectedType -> do
          inferredType <- lookupNameInContext n
          typesAreAlphaEquiv <- alphaEquivInContext inferredType expectedType
          unless typesAreAlphaEquiv do
            throwError (show (TypeErrorUnexpectedType inferredType expectedType))
          pure $ TypedVar n
      , getTerm = Var n
      }
  Node node ->
    let node' = bimap
          (bidirectionalCheckInferScoped . unScopedAST)
          (bidirectionalCheckInfer)
          node
    in CheckInfer
        { infer = inferSig node'
        , check = checkSig node'
        , getTerm = Node node
        }

bidirectionalCheckInferScoped ::
  ( Distinct n,
    Bifunctor sig,
    TypingSig binder ty sig m,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder,
    forall x. MonadError String (m x),
    MonadContext ty m
  ) =>
  Scoped binder (AST binder sig) n ->
  ScopedCheckInfer binder sig ty m n
bidirectionalCheckInferScoped (Scoped binder body) =
  case (assertExt binder, assertDistinct binder) of
    (Ext, Distinct) -> \mbinderType -> ScopedCheckInfer
      { scopedInfer = do
          ty <- extractTypeFromBinder binder mbinderType
          withBoundType binder ty do
            Scoped binder <$> bidirectionalInfer body
      , scopedCheck = \(Scoped binder' expectedType) -> do
          ty <- extractTypeFromBinder binder mbinderType
          case unifyPatterns binder binder' of
            SameNameBinders _binders -> do
              withBoundType binder ty do
                Scoped binder <$> bidirectionalCheck body expectedType
            RenameLeftNameBinder _binders renameL ->
              case (assertExt binder', assertDistinct binder') of
                (Ext, Distinct) ->
                  withBoundType binder' ty do
                    body' <- liftRMAboba (fromNameBinderRenaming renameL) body
                    Scoped binder' <$> bidirectionalCheck body' expectedType
            -- FIXME: RenameRightNameBinder, RenameBothNameBinders
            _ -> throwError "non-unifiable patterns"
      }

bindType
  :: (Sinkable ty, DExt n l, TypedPattern ty binder)
  => binder n l -> ty n -> Context ty n -> Context ty l
bindType binder ty (Context nameMap) = Context $ sink1 $ addNameBinder (extractExactlyOneBinder binder ty) ty nameMap

withBoundType
  :: (MonadContext ty m, Sinkable ty, DExt n l, TypedPattern ty binder)
  => binder n l -> ty n -> m l a -> m n a
withBoundType binder ty = localScoped (bindType binder ty)

liftRMAboba :: (MonadContext ty m, RelMonad f t, Distinct l) => (f n -> f l) -> t n -> m l (t l)
liftRMAboba f tn = do
  Context nameMap <- askScoped
  let scope = nameMapToScope nameMap
  pure $ liftRM scope f tn

--------------------------------------------------------------------------------

-- * Core Types

--------------------------------------------------------------------------------

-- | Typing context mapping names to types
newtype Context ty n = Context { unContext :: NameMap n (ty n) }

unScopedAST :: ScopedAST binder sig n -> Scoped binder (AST binder sig) n
unScopedAST (ScopedAST binder body) = Scoped binder body

-- | Scoped value with a binder
data Scoped binder (t :: S -> Type) (n :: S) where
  Scoped :: binder n l -> t l -> Scoped binder t n

mapBinder :: (forall x y. binder0 x y -> binder1 x y) -> Scoped binder0 t n -> Scoped binder1 t n
mapBinder f (Scoped bindernl tl) = Scoped (f bindernl) tl

mapScoped :: (forall x. t x -> t' x) -> Scoped binder t n -> Scoped binder t' n
mapScoped f (Scoped binder t) = Scoped binder (f t)

-- | Type errors
data TypeError ty
  = TypeErrorUnexpectedType ty ty
  | TypeErrorUnexpectedDependentType
  deriving (Show)


data TypedAST binder sig ty n where
  TypedVar :: {-# UNPACK #-} !(Name n) -> TypedAST binder sig ty n
  TypedNode :: sig (ScopedTypedAST binder sig ty n) (TypedAST binder sig ty n) -> ty n -> TypedAST binder sig ty n

type ScopedTypedAST binder sig ty = Scoped binder (TypedAST binder sig ty)

toAST :: (Bifunctor sig) => TypedAST binder sig ty n -> AST binder sig n
toAST (TypedVar n) = Var n
toAST (TypedNode node _) = Node (bimap toScopedAST toAST node)

toScopedAST :: (Bifunctor sig) => ScopedTypedAST binder sig ty n -> ScopedAST binder sig n
-- toScopedAST = mapScoped toAST
toScopedAST (Scoped binder typedAST) = ScopedAST binder (toAST typedAST)

typeOf :: (MonadContext ty m) => TypedAST binder sig ty n -> m n (ty n)
typeOf (TypedVar name) = lookupNameInContext name
typeOf (TypedNode _ ty) = pure ty

data CheckInfer binder sig ty m n = CheckInfer
  { check :: ty n -> m n (TypedAST binder sig ty n)
  , infer :: m n (TypedAST binder sig ty n)
  , getTerm :: AST binder sig n
  }

-- | Bidirectional check/infer for a scoped subterm.
--
-- The annotation (a 'Maybe' type for the bound variable) is supplied by the
-- parent typing rule. The resulting check/infer actions return the typed body
-- wrapped back in its binder, so the parent rule can recover both.
type ScopedCheckInfer' :: (S -> S -> Type) -> (Type -> Type -> Type) -> (S -> Type) -> (S -> Type -> Type) -> S -> Type
data ScopedCheckInfer' binder sig ty m n = ScopedCheckInfer
  { scopedCheck :: Scoped binder ty n -> m n (ScopedTypedAST binder sig ty n)
  , scopedInfer :: m n (ScopedTypedAST binder sig ty n)
  }

-- data ScopedCheckInfer' binder sig ty m n = ScopedCheckInfer
--   { scopedCheck :: Scoped binder ty n -> ScopedM binder m n (TypedAST binder sig ty)
--   , scopedInfer :: ScopedM binder m n (TypedAST binder sig ty)
--   }

-- data ScopedM binder m n t where
--   ScopedM :: binder n l -> m l (t l) -> ScopedM binder m n t

type ScopedCheckInfer binder sig ty m n = Maybe (ty n) -> ScopedCheckInfer' binder sig ty m n

-- | Typed name binders data structure
data TypedNameBinders ty n l where
  TypedNameBindersEmpty :: TypedNameBinders ty n n
  TypedNameBindersCons ::
    NameBinder n i -> ty n -> TypedNameBinders ty i l -> TypedNameBinders ty n l

--------------------------------------------------------------------------------

-- * Required Type Classes

--------------------------------------------------------------------------------

-- | Alpha equivalence class
class AlphaEquiv t where
  alphaEquiv :: (Distinct n) => Scope n -> t n -> t n -> Bool

-- | Default instance for Free Foil ASTs
instance
  (Bitraversable sig, ZipMatchK sig, UnifiablePattern binder, SinkableK binder) =>
  AlphaEquiv (AST binder sig)
  where
  alphaEquiv = FreeFoil.alphaEquiv

-- | Class for typed patterns
class TypedPattern ty pat | pat -> ty where
  extractPatternType :: pat n l -> Maybe (ty n)
  extractTypedBinders :: pat n l -> ty n -> TypedNameBinders ty n l

--------------------------------------------------------------------------------

-- * Generic Utilities

--------------------------------------------------------------------------------

-- | Extract type from a binder
extractTypeFromBinder ::
  (TypedPattern ty binder, AlphaEquiv ty, Distinct n, MonadError String (m n), MonadContext ty m) =>
  binder n l ->
  Maybe (ty n) ->
  m n (ty n)
extractTypeFromBinder binder Nothing =
  maybe (throwError "cannot infer without type annotation for pattern") pure $
    extractPatternType binder
extractTypeFromBinder binder (Just ty) =
  case extractPatternType binder of
    Nothing -> pure ty
    Just binderTy -> do
      typesAreAlphaEquiv <- alphaEquivInContext binderTy ty
      if typesAreAlphaEquiv
        then pure ty
        else throwError "type mismatch"

--------------------------------------------------------------------------------

-- * Main Bidirectional Type Checking API

--------------------------------------------------------------------------------

extractExactlyOneBinder :: TypedPattern ty pat => pat n l -> ty n -> NameBinder n l
extractExactlyOneBinder binder ty =
  case extractTypedBinders binder ty of
    TypedNameBindersCons extractedBinder _ty TypedNameBindersEmpty -> extractedBinder
    _ -> error "Expected exactly one binder"

shouldBe ::
  (AlphaEquiv ty, Distinct n, Show (ty n), MonadError String (m n), MonadContext ty m) =>
  ty n ->
  ty n ->
  m n ()
shouldBe actualType expectedType = do
  typesAreAlphaEquiv <- alphaEquivInContext actualType expectedType
  unless typesAreAlphaEquiv do
    throwError $ unlines
      [ "expected type"
      , "  " ++ show expectedType
      , "but got type"
      , "  " ++ show actualType
      , "when typechecking expression"
      ]

type MonadContext ty m = MonadScopedReader (Context ty) m

type MonadScopedReader :: (S -> Type) -> (S -> Type -> Type) -> Constraint
class (forall n. Monad (m n)) => MonadScopedReader t m | m -> t where
  askScoped :: m n (t n)
  localScoped :: forall l n a. (t n -> t l) -> m l a -> m n a
