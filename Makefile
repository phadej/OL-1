all :
	cabal new-build all

golden :
	cabal new-build golden
	(cd ol1 && $$(cabal-plan list-bin golden))

golden-accept :
	cabal new-build golden
	(cd ol1 && $$(cabal-plan list-bin golden) --accept)

doctest :
	doctest \
		-XDataKinds \
		-XDefaultSignatures \
		-XInstanceSigs \
		-XDeriveFoldable \
		-XDeriveFunctor \
		-XDeriveTraversable \
		-XFlexibleInstances \
		-XFunctionalDependencies \
		-XGADTs \
		-XKindSignatures \
		-XScopedTypeVariables \
		-XTypeOperators \
		-XTypeFamilies \
		OL-I/src
