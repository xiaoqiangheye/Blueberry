module Front.Typecheck where

import Data.Maybe
import Front.Ast
import Data.List
import qualified Data.Set as Set
import qualified Unbound.Generics.LocallyNameless as Unbound
import System.IO(withFile, IOMode(ReadMode), hGetContents, hPutStrLn, stderr)



-- type Ctx = [(String, Type)]

-- -- -- | Return the free variables in an expression
fv :: Term -> Set.Set String
fv (Var s) = Set.singleton s
fv (Lam s e) = Set.difference (fv e) (Set.singleton s)
fv (App e1 e2) = Set.union (fv e1) (fv e2)
fv (PI s t1 t2) = Set.difference (Set.union (fv t1) (fv t2)) (Set.singleton s)
fv (Ann x t) = fv x
-- fv (TrustMe) = Set.empty
-- fv (PrintMe) = Set.empty
-- fv (Let x e1 e2) = Set.difference (fv e2) (Set.singleton x)
fv TUnit = Set.empty
fv VUnit = Set.empty
fv TBool = Set.empty
fv (VBool _) = Set.empty
fv (If e1 e2 e3) = Set.union (Set.union (fv e1) (fv e2)) (fv e3)
fv (Pair e1 e2) = Set.union (fv e1) (fv e2)
fv (Sigma x e1 e2) = Set.difference (Set.union (fv e1) (fv e2)) (Set.singleton x)
-- fv (Prod e1 e2) = Set.union (fv e1) (fv e2)


subst :: Term -> String -> Term -> Term
subst n x (Var y) | x == y = n
                  | otherwise = Var y
subst n x (App e1 e2) = App (subst n x e1) (subst n x e2)
subst n x (Lam s e) | s == x = Lam s e
                    | otherwise = if Set.notMember s (fv n)
                                  then Lam s (subst n x e)
                                  else Lam newvar (subst n x (subst (Var newvar) s e))
 where newvar = pickFresh (Set.union (fv n) (fv e)) s

subst n x (PI s t1 t2) | s == x = PI s t1 t2
                       | otherwise = if Set.notMember s (fv n)
                                     then PI s t1 (subst n x t2)
                                     else PI newvar t1 (subst n x (subst (Var newvar) s t2))
 where newvar = pickFresh (Set.union (fv n) (fv t2)) s

subst n x (Ann v t) = subst n x v
subst n x (If a b1 b2) = If (subst n x a) (subst n x b1) (subst n x b2)
subst n x e = e


pickFresh :: Set.Set String -> String -> String
pickFresh s = pickFresh'
  where pickFresh' n | n `Set.notMember` s = n
        pickFresh' n                       = pickFresh' $ n ++ "'"



type Ctx = [Decl]


extendCtx :: Ctx -> Decl -> Ctx
extendCtx ctx delc = delc : ctx

extendCtxs :: Ctx -> [Decl] -> Ctx
extendCtxs ctx decl = decl ++ ctx

checkIsType :: Type -> Type -> Either String Type
checkIsType t1 t2 | t1 == t2 = Right t1
                  | otherwise = Left $ printTypeDoesNotMatch t1 t2


lookupTy :: Ctx -> String -> Either String Type
lookupTy [] x = Left ("failed to find variable " ++ x)
lookupTy ((TypeSig sig):ls) x | sigName sig == x = Right (sigType sig)
                              | otherwise = lookupTy ls x
lookupTy (d:ls) x = lookupTy ls x

lookupDef :: Ctx -> String -> Either String Term
lookupDef [] x = Left ("failed to find def " ++ x)
lookupDef ((Def x t):ls) y   | x == y = Right t
                             | otherwise = lookupTy ls y
lookupDef (d:ls) x = lookupDef ls x

infer :: Program -> Ctx -> IO ()
infer (Program p) = inferProgram $ reverse p


inferProgram :: [Decl] -> Ctx -> IO ()
inferProgram [] ctx = do putStrLn "Typechecking Success! Let's get some blueberry!"
inferProgram (def@(Def s t):ls) ctx =
    case lookupTy ctx s of
        Right tysig -> (do let t1 = checkType t ctx tysig
                           case t1 of
                            Right t2 -> inferProgram ls (extendCtx ctx def)
                            Left msg -> do putStrLn msg)
        Left msg -> do putStrLn msg

inferProgram (a@(TypeSig sig):ls) ctx = inferProgram ls (extendCtx ctx a)
inferProgram _ _ = return ()


printTypeSig :: Ctx -> IO ()
printTypeSig ((TypeSig sig): ls) = do
  print sig
  printTypeSig ls
printTypeSig _ = return ()

printTypeDoesNotMatch :: Type -> Type -> String
printTypeDoesNotMatch t1 t2 =
    "Type does not match: " ++ show t1 ++ "," ++ show t2

printVarDoesNotMatch x y =
     "Variable name does not match: " ++ x ++ "," ++ y



inferType :: Term -> Ctx -> Maybe Type -> Either String Type
inferType (Var x) ctx Nothing = lookupTy ctx x

inferType TUnit ctx Nothing = Right Type

inferType VUnit ctx Nothing = Right TUnit

inferType TBool ctx Nothing = Right Type

inferType (VBool _) ctx Nothing = Right TBool

inferType (If a b1 b2) ctx Nothing = do
    t <- checkType a ctx TBool
    ty <- inferType b1 ctx Nothing
    t2 <- eval ty ctx
    checkType b2 ctx t2


inferType (If a b1 b2) ctx (Just t) = do
    checkType a ctx TBool
    case a of
      (Var x) -> do
        ttrue <- eval (subst (VBool True) x t) ctx
        tfalse <- eval (subst (VBool False) x t) ctx
        --Left $ show ttrue
        checkType b1 ctx ttrue
        checkType b2 ctx tfalse
        return t
      _ -> do t1 <- eval t ctx
              checkType b1 ctx t1
              checkType b2 ctx t1
              return t

inferType Type ctx Nothing  = Right Type

inferType (PI x tyA tyB) ctx Nothing = do
    type2 <- checkType tyA ctx Type
    t2 <- eval type2 ctx
    checkType tyB (extendCtx ctx (mkSig x t2)) Type


inferType (Ann x t) ctx Nothing = do
    type1 <- checkType t ctx Type
    t1 <- eval type1 ctx
    checkType x ctx t1

inferType (App e1 e2) ctx Nothing = do
    type1 <- inferType e1 ctx Nothing
    (x, tyA, tyB) <- ensurePi type1
    type2 <- checkType e2 ctx tyA
    eval (subst e2 x tyB) ctx


inferType (Sigma x tyA tyB) ctx Nothing = do
    t1 <- checkType tyA ctx Type
    type1 <- eval t1 ctx
    checkType tyB (extendCtx ctx (mkSig x type1)) Type
    return Type

inferType (Pair t1 t2) ctx (Just t@(Sigma x tyA tyB)) = do
    checkType t1 ctx tyA
    tyB' <- eval (subst t1 x tyB) ctx
    checkType t2 ctx tyB'
    return t

inferType (Lam x e1) ctx (Just (PI x1 tyA tyB)) = do
    (if x == x1 || x1 == "_"
    then do tyA' <- eval tyA ctx
            tyB' <- eval tyB ctx
            checkType e1 (extendCtx ctx (mkSig x tyA')) tyB'
    else Left (printVarDoesNotMatch x x1))


inferType (Lam x e1) ctx (Just t) = Left (printTypeDoesNotMatch (Lam x e1) t)


inferType Refl ctx (Just t@(TyEq a b)) = 
    if equate a b 
    then Right t 
    else Left (printTypeDoesNotMatch Refl t)

inferType (TyEq a b) ctx _ = do
    tA <- inferType a ctx Nothing
    tB <- inferType b ctx Nothing
    checkIsType tA tB

inferType e ctx (Just t) = do typ <- inferType e ctx Nothing
                              t1 <- eval t ctx
                              t2 <- eval typ ctx
                              checkIsType t1 t2


-- inferType (Subst a y) ctx (Just tA) =
--     do tyB <- inferType y ctx Nothing
--        (x,x1) <- ensureTyEQ tyB
--        case (x,x1) of
--            (Var x,_) ->
--                     case checkType a ctx (subst a2 x tA) of
--                        Nothing -> case checkType a ctx (subst x a2 tA) of
-- 									    Nothing -> Nothing
-- 										Just e -> Just tA
-- 					   Just e -> Just tA
-- 		   (_, Var x) -> case checkType a ctx (subst a2 x tA) of
--                        Nothing -> case checkType a ctx (subst x a2 tA) of
-- 									    Nothing -> Nothing
-- 										Just e -> Just tA
-- 					   Just e -> Just tA


-- inferType (Contra a) ctx (Just B) = 
-- 	do inferType a ctx A = 


ensureTyEQ (TyEq a b) = do return (a,b)
ensureTyEQ _ = Left "Not match Equal Type"



ensurePi :: Type -> Either String (String, Type, Type)
ensurePi t@(PI s tyA tyB) = do return (s, tyA, tyB)
ensurePi t = Left "Not match PI"



eval :: Term -> Ctx -> Either String Term
eval (If (VBool True) b1 b2) _ = Right b1
eval (If (VBool False) b1 b2) _ = Right b2
eval (If a b1 b2) ctx = do t <- eval a ctx
                           case t of
                            (VBool _) -> eval (If t b1 b2) ctx
                            _ -> return $ If t b1 b2
eval TBool _ = Right TBool
eval (Sigma x t1 t2) ctx = do t1' <- eval t1 ctx
                              t2' <- eval t2 ctx
                              return $ Sigma x t1' t2'
eval TUnit _ = Right TUnit
eval VUnit _ = Right VUnit
eval (VBool True) _ = Right $ VBool True
eval (VBool False) _ = Right $ VBool False
eval (Ann e t) ctx = eval e ctx
eval Type _ = Right Type
eval (Var x) ctx = case lookupDef ctx x of
                        Right e -> Right e
                        Left _ -> return $ Var x
eval (PI x tyA tyB) ctx = do tyA' <- eval tyA ctx
                             tyB' <- eval tyB ctx
                             return $ PI x tyA' tyB'
eval (Lam x e) ctx = do u <- eval e ctx                    
                        return $ Lam x u
eval (App e1 e2) ctx = do e1' <- eval e1 ctx
                          case e1' of
                            Lam x e -> return $ subst e2 x e
                            _ -> do e2' <- eval e2 ctx
                                    return $ App e1' e2'


equate :: Term -> Term -> Bool
equate Type Type = True
equate TUnit TUnit = True
equate VUnit VUnit = True
equate TBool TBool = True
equate (VBool x) (VBool y) = x == y
equate (Var x) (Var y) = x == y
equate (Lam x e) (Lam x1 e1) = equate e e1
equate (Ann x _) (Ann x1 _) = equate x x1
equate (PI x tyA tyB) (PI y tyA' tyB') = equate tyA tyA' && equate tyB tyB'
equate (If a b1 b2) (If a' b1' b2') = equate a a' && equate b1 b1' && equate b2 b2'
equate (App e1 e2) (App e1' e2') = equate e1 e1' && equate e2 e2'
equate (Sigma x t1 t2) (Sigma y t1' t2') = equate t1 t1' && equate t2 t2'
equate (Let x t1 t2) (Let y t1' t2') = x == y && equate t1 t1' && equate t2 t2'

checkType :: Term -> Ctx -> Type -> Either String Type
checkType e ctx t = inferType e ctx (Just t)