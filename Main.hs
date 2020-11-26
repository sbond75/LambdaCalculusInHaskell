data Term = TmVar {-Variable-}
				Index {-de Bruijn index-} 
				Int {-Total length of context in which this variable occurs-}
			| TmAbs {-Abstraction-}
				String {-Name-}
				Term
			| TmApp Term Term
			deriving Show

type Index = Int

printtm ctx t = case t of
	TmAbs x t1 -> let (ctx', x') = pickfreshname ctx x in do {
		putStr "(lambda "; putStr x'; putStr ". "; printtm ctx' t1; putStr ")" }
	TmApp t1 t2 -> do {
		putStr "("; printtm ctx t1; putStr " "; printtm ctx t2; putStr ")" }
	TmVar x n -> if ctxlength ctx == n then putStr (index2name ctx x) else putStr ("[bad index: " ++ (show n) ++ ", needed " ++ (show (ctxlength ctx)) ++ "]")
	
type Context = [(String, Binding)]
data Binding = NameBind {-The only ctor for now-}

ctxlength :: Context -> Int
ctxlength ctx = length ctx

index2name :: Context -> Index -> String
index2name ctx index = case ctx of
	[] -> "[empty ctx]"
	(x@(name,binding):xs) -> case index of
		0 -> name
		_ -> index2name xs (index-1)

pickfreshname :: Context -> String -> (Context, String)
pickfreshname ctx hint = if isnamebound ctx x then pickfreshname ctx (x ++ "'") else (((x,NameBind):ctx), x)
	where x = hint

isnamebound :: Context -> String -> Bool
isnamebound ctx x = case ctx of
	[] -> False
	((name,binding):xs) -> if name == x then True else isnamebound xs x

{-printtm :: Context -> Term -> IO ()
printtm ctx (TmVar x len) = do let name = index2name ctx x in print name
printtm ctx (TmAbs name t1) = do
	print name; printtm t1
printtm ctx (TmApp t1 t2) = do
	printtm t1; print "; "; printtm t2-}

termShift :: Int -> Term -> Term
termShift d t = walk 0 t 
	where walk = \c t -> case t of
		TmVar x n -> if x >= c then TmVar (x+d) (n+d) else TmVar x (n+d)
		TmAbs x t1 -> TmAbs x (walk (c+1) t1)
		TmApp t1 t2 -> TmApp (walk c t1) (walk c t2)

termSubst :: Int -> Term -> Term -> Term
termSubst j s t = walk 0 t 
	where walk = \c t -> case t of
		TmVar x n -> if x==j+c then termShift c s else TmVar x n
		TmAbs x t1 -> TmAbs x (walk (c+1) t1)
		TmApp t1 t2 -> TmApp (walk c t1) (walk c t2)

termSubstTop s t = termShift (-1) (termSubst 0 (termShift 1 s) t)

{- Evaluation -}

isval ctx t = case t of
	TmAbs _ _ -> True
	_ -> False

eval1 :: Context -> Term -> Either String Term
eval1 ctx t = case t of
	TmApp (TmAbs x t12) v2 | isval ctx v2 -> Right $ termSubstTop v2 t12
	TmApp v1 t2 | isval ctx v1 -> case eval1 ctx t2 of
		Left err -> Left err
		Right t2' -> Right $ TmApp v1 t2'
	TmApp t1 t2 -> case eval1 ctx t1 of
		Left err -> Left err
		Right t1' -> Right $ TmApp t1' t2
	_ -> Left "No rule applies"

eval :: Context -> Term -> Term
eval ctx t = case eval1 ctx t of
	Right t' -> eval ctx t'
	Left err -> t


{-repl :: IO ()
repl = do
	ctx = [("l", NameBind)]
	putStr "> "
	x <- read
	eval ctx x-}

{-main = repl-}

{- "The term λx. λy. x, sometimes called the K combinator, is written as λ λ 2 with De Bruijn indices." ( https://en.wikipedia.org/wiki/De_Bruijn_index ) -}
{- Here we apply the k combinator to some random lambda -}
test1 = do
  printtm ctx (eval ctx (TmApp (TmAbs "L" (TmAbs "LL" (TmVar 2 3))) (TmAbs "LLL" (TmVar 2 3))))
  putStrLn ""
  where ctx = [("l", NameBind)]

-- Ben: We don't have numbers! only values that aren't debruijn reference things are lambdas (TmAbs).. so this is JUST THE SIMPLEST form of lambda calculus possible. We can extend it though.
test2 = (TmApp (TmApp s i) i)
  where s = (TmAbs "x" (TmAbs "y" (TmAbs "z" (TmApp (TmApp (TmVar 3 1) (TmVar 1 1)) (TmApp (TmVar 2 1) (TmVar 1 1)))))) --  λ λ λ 3 1 (2 1)                  =         λ (λ (λ (3 1) (2 1)))
        i = (TmAbs "x" (TmVar 1 1))

test2_ = eval [] test2

main = test1
