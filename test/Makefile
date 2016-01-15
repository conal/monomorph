HERM = hermit Examples.hs -v0 -opt=Monomorph.Stuff

default: go

%.cont:
	(cat settings.hss ; echo "rhs-of '$*" ; cat recipe.hss) > out/script.hss
	$(HERM) out/script.hss

%.bare:
	(cat settings.hss ; echo "rhs-of '$*") > out/script.hss
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

##

timing-mapt:
	make mapt1.time3 > out/mapt1
	make mapt2.time3 > out/mapt2
	make mapt4.time3 > out/mapt4
	make mapt8.time3 > out/mapt8
	make mapt16.time3 > out/mapt16

timing-mapv:
	make mapv1.time3 > out/mapv1
	make mapv2.time3 > out/mapv2
	make mapv4.time3 > out/mapv4
	make mapv8.time3 > out/mapv8
	make mapv16.time3 > out/mapv16

timing-sumt:
	make sumt1.time3 > out/sumt1
	make sumt2.time3 > out/sumt2
	make sumt4.time3 > out/sumt4
	make sumt8.time3 > out/sumt8
	make sumt16.time3 > out/sumt16

timing-sumt-huge:
	make sumt16.time3 > out/sumt16
	make sumt32.time3 > out/sumt32
	make sumt64.time3 > out/sumt64
	make sumt128.time3 > out/sumt128
	make sumt256.time3 > out/sumt256

timing-sumv:
	make sumv1.time3 > out/sumv1
	make sumv2.time3 > out/sumv2
	make sumv4.time3 > out/sumv4
	make sumv8.time3 > out/sumv8
	make sumv16.time3 > out/sumv16

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
