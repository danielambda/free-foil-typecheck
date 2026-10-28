{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DerivingVia #-}

module FreeFoilTypecheck.SystemF.TypingSig where

import Control.Monad.Foil hiding (AlphaEquiv)
import Control.Monad.Free.Foil
import FreeFoilTypecheck.SystemF.Syntax
import FreeFoilTypecheck.SystemF.TypecheckGen
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.Reader

deriving instance Show (TermSig (ScopedTypedAST (FoilPattern Term) TermSig Term n) (TypedAST (FoilPattern Term) TermSig Term n))
deriving instance Show (FoilPattern Term n l)
deriving instance Show (TypedAST (FoilPattern Term) TermSig Term n)
deriving instance Show (ScopedTypedAST (FoilPattern Term) TermSig Term n)

--------------------------------------------------------------------------------

-- * TypingSig Instance for System F

--------------------------------------------------------------------------------

newtype Typecheck n a = Typecheck { runTypecheck :: Context Term n -> Either String a }
  deriving (Functor, Applicative, Monad, MonadError String) via (ReaderT (Context Term n) (Either String))

instance MonadScopedReader (Context Term) Typecheck where
  askScoped = Typecheck Right
  localScoped f (Typecheck typecheck) = Typecheck $ typecheck . f

instance
  (forall n. Show (TypeError (Term n))) =>
  TypingSig (FoilPattern Term) Term TermSig Typecheck
  where
  --------------------------------------------------------------------------------
  -- Type Checking Rules
  --------------------------------------------------------------------------------

  checkSig = \case
    -- Type abstraction: Γ ⊢ ΛX.t ⇐ ∀X.T
    ETAbsSig body -> \case
      Term (TForAll x bodyType) -> do
        sc <- scopedCheck (body (Just (Term TType))) (Scoped x (Term bodyType))
        pure $ TypedNode (ETAbsSig sc) (Term (TForAll x bodyType))
      _ -> throwError "unexpected type abstraction"
    -- Type application
    ETAppSig e t -> \expectedType -> do
      tt <- check t (Term TType)
      et <- infer e
      typeOf et >>= \case
        Term (TForAll (FoilPatternVar x) bodyType) -> do
          let subst = addSubst identitySubst x (toAST tt)
          actualType <- substituteInContext subst bodyType
          Term actualType `shouldBe` expectedType
          pure $ TypedNode (ETAppSig et tt) (Term actualType)
        _ -> throwError "expected a type abstraction"

    -- Lambda abstraction: Γ ⊢ λx:A. t ⇐ A → B
    EAbsSig body -> \case
      Term (TArrow x expectedBodyType) -> do
        Scoped c b <- scopedInfer (body (Just (Term x)))
        case (assertDistinct c, assertExt c) of
          (Distinct, Ext) -> do
            bType <- withBoundType c (Term x) $ typeOf b
            b' <- unsinkType bType
            b' `shouldBe` Term expectedBodyType
            pure $ TypedNode (EAbsSig (Scoped c b)) (Term (TArrow x expectedBodyType))
      t -> throwError $ "unexpected abstraction" <> show t
    -- Let binding
    ELetSig e body -> \expectedType -> do
      typedE <- infer e
      a <- typeOf typedE
      Context scope <- askScoped
      let scopedExpectedType = withFresh (nameMapToScope scope) \binder ->
            Scoped (FoilPatternVar binder) (sink expectedType)
      typedBody <- scopedCheck (body (Just a)) scopedExpectedType
      pure $ TypedNode (ELetSig typedE typedBody) expectedType

    -- Default case
    sig -> defaultCheckSig sig

  --------------------------------------------------------------------------------
  -- Type Inference Rules
  --------------------------------------------------------------------------------

  inferSig = \case
    -- Literals
    ETrueSig -> pure $ TypedNode ETrueSig (Term TBool)
    EFalseSig -> pure $ TypedNode EFalseSig (Term TBool)
    ENatSig n -> pure $ TypedNode (ENatSig n) (Term TNat)
    -- Arithmetic operations
    EAddSig l r -> do
      typedL <- check l (Term TNat)
      typedR <- check r (Term TNat)
      pure $ TypedNode (EAddSig typedL typedR) (Term TNat)
    ESubSig l r -> do
      typedL <- check l (Term TNat)
      typedR <- check r (Term TNat)
      pure $ TypedNode (ESubSig typedL typedR) (Term TNat)

    -- Conditionals
    EIfSig cond thenBranch elseBranch -> do
      typedCond <- check cond (Term TBool)
      typedThenBranch <- infer thenBranch
      thenType <- typeOf typedThenBranch
      typedElseBranch <- check elseBranch thenType
      pure $ TypedNode (EIfSig typedCond typedThenBranch typedElseBranch) thenType

    -- Zero test
    EIsZeroSig e -> do
      typedE <- check e (Term TNat)
      pure $ TypedNode (EIsZeroSig typedE) (Term TBool)

    -- Type annotation
    -- t : T
    -- T : Type
    ETypedSig e t -> do
      typedT <- check t (Term TType)
      let t' = Term $ getTerm t
      typedE <- check e t'
      pure $ TypedNode (ETypedSig typedE typedT) t'

    -- Let binding: Γ ⊢ let x = e in body ⇒ B
    ELetSig e body -> do
      typedE <- infer e
      eType <- typeOf typedE
      Scoped x typedBody <- scopedInfer (body (Just eType))
      case (assertDistinct x, assertExt x) of
        (Distinct, Ext) -> do
          bodyType' <- withBoundType x eType $ typeOf typedBody
          bodyType <- unsinkType bodyType'
          pure $ TypedNode (ELetSig typedE (Scoped x typedBody)) bodyType

    -- For loop
    EForSig e1 e2 body -> do
      typedE1 <- check e1 (Term TNat)
      typedE2 <- check e2 (Term TNat)
      Scoped x typedBody <- scopedInfer (body (Just (Term TNat)))
      case (assertDistinct x, assertExt x) of
        (Distinct, Ext) -> do
          bodyType' <- withBoundType x (Term TNat) $ typeOf typedBody
          bodyType <- unsinkType bodyType'
          pure $ TypedNode (EForSig typedE1 typedE2 (Scoped x typedBody)) bodyType

    -- Function application: Γ ⊢ f x ⇒ B
    EAppSig f x -> do
      typedF <- infer f
      typeOf typedF >>= \case
        Term (TArrow a b) -> do
          typedX <- check x (Term a)
          pure $ TypedNode (EAppSig typedF typedX) (Term b)
        _ -> throwError "not a function"

    -- Lambda abstraction (with annotation)
    EAbsSig body -> do
      Scoped binder typedBody <- scopedInfer (body Nothing)
      case binder of
        FoilPatternAsc x (Term xType) ->
          case (assertDistinct x, assertExt x) of
            (Distinct, Ext) -> do
              bodyType' <- withBoundType binder (Term xType) $ typeOf typedBody
              Term bodyType <- unsinkType bodyType'
              pure $ TypedNode (EAbsSig (Scoped binder typedBody)) (Term (TArrow xType bodyType))
        _ -> throwError "cannot infer type of unannotated lambda"

    -- Type application
    ETAppSig body arg -> do
      typedArg <- check arg (Term TType)
      typedBody <- infer body
      typeOf typedBody >>= \case
        Term (TForAll (FoilPatternVar x) bodyType) -> do
          let argType = getTerm arg
          let subst = addSubst identitySubst x argType
          actualType <- substituteInContext subst bodyType
          pure $ TypedNode (ETAppSig typedBody typedArg) (Term actualType)
        _ -> throwError "expected a polymorphic type"

    -- Type abstraction
    -- ΛX.λx.x  :  forall X. X -> X
    -- body = λx.x : X -> X
    ETAbsSig body -> do
      Scoped x typedBody <- scopedInfer (body (Just (Term TType)))
      case (assertDistinct x, assertExt x) of
        (Distinct, Ext) -> do
          Term bodyType <- withBoundType x (Term TType) $ typeOf typedBody
          pure $ TypedNode (ETAbsSig (Scoped x typedBody)) (Term (TForAll x bodyType))

    -- Type constructors
    TBoolSig -> pure $ TypedNode TBoolSig (Term TType)
    TNatSig -> pure $ TypedNode TNatSig (Term TType)
    TUVarSig v -> pure $ TypedNode (TUVarSig v) (Term TType)
    TTypeSig -> pure $ TypedNode TTypeSig (Term TType)
    -- Type-level forall
    TForAllSig body -> do -- forall X. T
      typedBody <- scopedInfer (body (Just (Term TType)))
      pure $ TypedNode (TForAllSig typedBody) (Term TType)

    -- Arrow type
    TArrowSig a b -> do
      typedA <- check a (Term TType)
      typedB <- check b (Term TType)
      pure $ TypedNode (TArrowSig typedA typedB) (Term TType)

--------------------------------------------------------------------------------

-- * Utility Functions

--------------------------------------------------------------------------------

-- | Unsink a type from a larger scope to a smaller one
unsinkType :: (Distinct l, forall x. MonadError String (m x), MonadContext Term m) => Term l -> m n (Term n)
unsinkType type_ = do
  Context nameMap <- askScoped
  case unsinkAST (nameMapToScope nameMap) (convertTermToAST type_) of
    Nothing -> throwError "dependent types!"
    Just type'' -> return (Term type'')

-- | Convert Term to AST
convertTermToAST :: Term n -> AST (FoilPattern Term) TermSig n
convertTermToAST (Term ast) = ast

--------------------------------------------------------------------------------

-- * Typeclass Instances

--------------------------------------------------------------------------------

instance TypedPattern ty (FoilPattern ty) where
  extractPatternType (FoilPatternVar _) = Nothing
  extractPatternType (FoilPatternAsc _ ty) = Just ty
  extractTypedBinders (FoilPatternVar binder) ty =
    TypedNameBindersCons binder ty TypedNameBindersEmpty
  extractTypedBinders (FoilPatternAsc binder ty) _ =
    TypedNameBindersCons binder ty TypedNameBindersEmpty

deriving newtype instance AlphaEquiv Term
