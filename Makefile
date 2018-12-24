all : 
	cabal new-build all

golden : 
	cabal new-build golden
	(cd ol1 && $$(cabal-plan list-bin golden))

doctest : 
	doctest -XDefaultSignatures -XDeriveFunctor -XDeriveFoldable -XDeriveTraversable -XGADTs -XFunctionalDependencies -XDataKinds -XKindSignatures -XTypeOperators -XFlexibleInstances src
