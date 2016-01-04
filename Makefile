# include ../my-cabal-make.inc

install:
	cabal install --force-reinstalls -j1 --disable-documentation

tags: dist
	cd src ; find . -name '*.*hs' | egrep -v 'Junk|Old|Unused|Setup\.lhs' | xargs hasktags -e
