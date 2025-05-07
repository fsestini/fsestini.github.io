.PHONY: default
default:
	cabal run site build

.PHONY: watch
watch:
	cabal run site watch
