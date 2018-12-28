all :
	cabal new-build all

fixtures :
	cabal new-build fixtures
	(cd OL-I && $$(cabal-plan list-bin fixtures))

fixtures-accept :
	cabal new-build fixtures
	(cd OL-I && $$(cabal-plan list-bin fixtures) --accept)

ghcid-OL-I :
	ghcid -c 'cabal new-repl OL-I'

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
