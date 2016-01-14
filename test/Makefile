HERM = hermit Examples.hs -v0 -opt=Monomorph.Stuff

default: go

%.cont:
	(cat settings.hss ; echo "rhs-of '$*" ; cat recipe.hss) > out/script.hss
	$(HERM) out/script.hss

%.done:
	echo "" | make $*.cont ; echo

%.time:
	time make $*.done

%.time3:
	make $*.time
	make $*.time
	make $*.time

compile:
	cd .. ; make

compile-circat:
	cd ~/Tabula/Haskell/circat ; make

compile-extras:
	cd ~/Tabula/Haskell/hermit-extras ; make

compile-all: compile-circat compile-extras compile-mono

## Older targets

go:
	$(HERM) Go.hss

timing3:
	make timing
	make timing
	make timing

timing:
	time make go-resume

go-done:
	echo "" | make go ; echo

go-resume:
	$(HERM) Go.hss resume

bare:
	$(HERM) settings.hss
