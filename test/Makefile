HERM = hermit Examples.hs -v0 -opt=Monomorph.Stuff

doit:
	time $(HERM) Go.hss resume && ./TreeTest

reify-done:
	echo "" | make reify ; echo

no-reify-done:
	echo "" | make no-reify ; echo

dont-done:
	echo "" | make dont ; echo

foo-done:
	echo "" | make foo ; echo

reify:
	$(HERM) Go.hss

no-reify:
	$(HERM) GoNoReify.hss

dont:
	$(HERM) Dont.hss

foo:
	$(HERM) Foo.hss

compile:
	cd ../..; make

