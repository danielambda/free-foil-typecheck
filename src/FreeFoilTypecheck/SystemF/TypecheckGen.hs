module FreeFoilTypecheck.SystemF.TypecheckGen
  ( Context'
  , AlphaEquiv(..)
  , TypingSig(..)
  , defaultCheckSig
  , TypedPattern(..)
  , bidirectionalCheck
  , bidirectionalInfer
  , Scoped(..)
  , mapBinder
  , TypeError(..)
  , TypedNameBinders(..)
  , UserCheckInfer(..)
  , shouldBe
  ) where

import Control.Monad (unless)
import Control.Monad.Foil hiding (AlphaEquiv)
import Control.Monad.Free.Foil qualified as FreeFoil (alphaEquiv)
import Control.Monad.Foil.Relative
import Control.Monad.Free.Foil hiding (alphaEquiv)
import Data.Bitraversable (Bitraversable)
import Data.Kind (Type)
import Data.ZipMatchK (ZipMatchK)
import Data.Bifunctor (bimap, Bifunctor)

-- | Main typing signature class
class
  (forall n. Show (TypeError (ty n)), AlphaEquiv ty) =>
  TypingSig binder ty sig
  where
  checkSig ::
    (Distinct n) =>
    Context' ty n ->
    sig (UserScopedCheckInfer binder ty n) (UserCheckInfer ty n) ->
    ty n ->
    Either String ()
  checkSig = defaultCheckSig

  inferSig ::
    (Distinct n) =>
    Context' ty n ->
    sig (UserScopedCheckInfer binder ty n) (UserCheckInfer ty n) ->
    Either String (ty n)

defaultCheckSig ::
  (TypingSig binder ty sig, Distinct n) =>
  Context' ty n ->
  sig (UserScopedCheckInfer binder ty n) (UserCheckInfer ty n) ->
  ty n ->
  Either String ()
defaultCheckSig ctx node expectedType = do
  inferredType <- inferSig ctx node
  unless (alphaEquiv (nameMapToScope ctx) inferredType expectedType) $
    Left (show (TypeErrorUnexpectedType inferredType expectedType))

inferSigInternal :: (TypingSig binder ty sig, Distinct n, Bifunctor sig) =>
  Context' ty n ->
  sig (ScopedCheckInfer binder ty n) (CheckInfer ty n) ->
  Either String (ty n)
inferSigInternal ctx node = inferSig ctx (toUser node)

checkSigInternal :: (TypingSig binder ty sig, Distinct n, Bifunctor sig) =>
  Context' ty n ->
  sig (ScopedCheckInfer binder ty n) (CheckInfer ty n) ->
  ty n ->
  Either String ()
checkSigInternal ctx node = checkSig ctx (toUser node)

fromUserCheckInfer :: UserCheckInfer ty n -> CheckInfer ty n
fromUserCheckInfer UserCheckInfer{ check, infer } = CheckInfer
  { checkInternal = check, inferInternal = infer }

toUserCheckInfer :: CheckInfer ty n -> UserCheckInfer ty n
toUserCheckInfer CheckInfer{ checkInternal, inferInternal } = UserCheckInfer
  { check = checkInternal, infer = inferInternal }

toUserScopedCheckInfer :: ScopedCheckInfer binder ty n -> UserScopedCheckInfer binder ty n
toUserScopedCheckInfer scopedCheckInfer mbinder = toUserCheckInfer $ scopedCheckInfer mbinder

toUser :: Bifunctor sig => sig (ScopedCheckInfer binder ty n) (CheckInfer ty n) -> sig (UserScopedCheckInfer binder ty n) (UserCheckInfer ty n)
toUser = bimap toUserScopedCheckInfer toUserCheckInfer

bidirectionalInfer ::
  forall ty binder sig n.
  ( Distinct n,
    Bifunctor sig,
    AlphaEquiv ty,
    TypingSig binder ty sig,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder
  ) =>
  Context' ty n ->
  AST binder sig n ->
  Either String (ty n)
bidirectionalInfer scope t = inferInternal $ bidirectionalCheckInfer scope t

bidirectionalCheck ::
  forall ty binder sig n.
  ( Distinct n,
    Bifunctor sig,
    AlphaEquiv ty,
    TypingSig binder ty sig,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder
  ) =>
  Context' ty n ->
  AST binder sig n ->
  ty n -> Either String ()
bidirectionalCheck scope t = checkInternal $ bidirectionalCheckInfer scope t

bidirectionalCheckInfer ::
  forall ty binder sig n.
  ( Distinct n,
    Bifunctor sig,
    TypingSig binder ty sig,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder
  ) =>
  Context' ty n ->
  AST binder sig n ->
  CheckInfer ty n
bidirectionalCheckInfer scope = \case
  Var n ->
    let inferredType = lookupName n scope
     in CheckInfer
          { inferInternal = pure inferredType
          , checkInternal = \expectedType ->
              unless (alphaEquiv (nameMapToScope scope) inferredType expectedType) do
                Left (show (TypeErrorUnexpectedType inferredType expectedType))
          }
  Node node ->
    let node' = bimap
          (bidirectionalCheckInferScoped scope . unScopedAST)
          (bidirectionalCheckInfer scope)
          node
        ci = CheckInfer
          { inferInternal = inferSigInternal scope node'
          , checkInternal = checkSigInternal scope node'
          }
    in ci

data TypedAST binder ty sig n where
  TypedVar :: Name n -> ty n -> TypedAST binder ty sig n
  TypedNode
    :: sig (Scoped binder (TypedAST binder ty sig) n) (TypedAST binder ty sig n)
    -> ty n
    -> TypedAST binder ty sig n

bidirectionalCheckInferScoped ::
  ( Distinct n,
    Bifunctor sig,
    TypingSig binder ty sig,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder
  ) =>
  Context' ty n ->
  Scoped binder (AST binder sig) n ->
  ScopedCheckInfer binder ty n
bidirectionalCheckInferScoped scope (Scoped binder body) =
  case (assertExt binder, assertDistinct binder) of
    (Ext, Distinct) -> \mbinderType -> CheckInfer
      { inferInternal = do
          ty <- extractTypeFromBinder scope binder mbinderType
          -- TODO add all bound variables to the scope, not just when there is only one of them
          let scope' = sink <$> addNameBinder (extractExactlyOneBinder binder ty) ty scope
          Scoped binder <$> bidirectionalInfer scope' body
      , checkInternal = \(Scoped binder' expectedType) -> do
          ty <- extractTypeFromBinder scope binder mbinderType
          case unifyPatterns binder binder' of
            SameNameBinders _binders -> do
              let scope' = sink <$> addNameBinder (extractExactlyOneBinder binder ty) ty scope
              bidirectionalCheck scope' body expectedType
            RenameLeftNameBinder _binders renameL ->
              case (assertExt binder', assertDistinct binder') of
                (Ext, Distinct) -> do
                  let scope' = sink <$> addNameBinder (extractExactlyOneBinder binder' ty) ty scope
                  let body' = liftRM (nameMapToScope scope') (fromNameBinderRenaming renameL) body
                  bidirectionalCheck scope' body' expectedType
            -- FIXME: RenameRightNameBinder, RenameBothNameBinders
            _ -> Left "non-unifiable patterns"
      }

--------------------------------------------------------------------------------

-- * Core Types

--------------------------------------------------------------------------------

-- | Typing context mapping names to types
type Context' ty n = NameMap n (ty n)

unScopedAST :: ScopedAST binder sig n -> Scoped binder (AST binder sig) n
unScopedAST (ScopedAST binder body) = Scoped binder body

-- | Scoped value with a binder
data Scoped binder (t :: S -> Type) (n :: S) where
  Scoped :: binder n l -> t l -> Scoped binder t n

mapBinder :: (forall x y. binder0 x y -> binder1 x y) -> Scoped binder0 t n -> Scoped binder1 t n
mapBinder f (Scoped bindernl tl) = Scoped (f bindernl) tl

-- | Type errors
data TypeError ty
  = TypeErrorUnexpectedType ty ty
  | TypeErrorUnexpectedDependentType
  deriving (Show)

data UserCheckInfer ty n = UserCheckInfer
  { check :: ty n -> Either String ()
  , infer :: Either String (ty n)
  }

data CheckInfer ty n = CheckInfer
  { checkInternal :: ty n -> Either String ()
  , inferInternal :: Either String (ty n)
  }

type UserScopedCheckInfer binder ty n = Maybe (ty n) -> UserCheckInfer (Scoped binder ty) n

type ScopedCheckInfer binder ty n = Maybe (ty n) -> CheckInfer (Scoped binder ty) n

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
class TypedPattern ty pat where
  extractPatternType :: pat n l -> Maybe (ty n)
  extractTypedBinders :: pat n l -> ty n -> TypedNameBinders ty n l

--------------------------------------------------------------------------------

-- * Generic Utilities

--------------------------------------------------------------------------------

-- | Extract type from a binder
extractTypeFromBinder ::
  (TypedPattern ty binder, AlphaEquiv ty, Distinct n) =>
  Context' ty n ->
  binder n l ->
  Maybe (ty n) ->
  Either String (ty n)
extractTypeFromBinder _scope binder Nothing =
  maybe (Left "cannot infer without type annotation for pattern") Right $
    extractPatternType binder
extractTypeFromBinder scope binder (Just ty) =
  case extractPatternType binder of
    Nothing -> Right ty
    Just binderTy ->
      if alphaEquiv (nameMapToScope scope) binderTy ty
        then Right ty
        else Left "type mismatch"

--------------------------------------------------------------------------------

-- * Main Bidirectional Type Checking API

--------------------------------------------------------------------------------

extractExactlyOneBinder :: TypedPattern ty pat => pat n l -> ty n -> NameBinder n l
extractExactlyOneBinder binder ty =
  case extractTypedBinders binder ty of
    TypedNameBindersCons extractedBinder _ty TypedNameBindersEmpty -> extractedBinder
    _ -> error "Expected exactly one binder"

shouldBe ::
  (AlphaEquiv ty, Distinct n, Show (ty n)) =>
  (Context' ty n, ty n) ->
  ty n ->
  Either String ()
shouldBe (scope, actualType) expectedType =
  unless (alphaEquiv (nameMapToScope scope) actualType expectedType) do
    Left $ unlines
      [ "expected type"
      , "  " ++ show expectedType
      , "but got type"
      , "  " ++ show actualType
      , "when typechecking expression"
      ]

