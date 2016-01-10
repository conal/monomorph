HERM = hermit Examples.hs -v0 -opt=Monomorph.Stuff

go:
	$(HERM) Go.hss

go-done:
	echo "" | make go ; echo

go-resume:
	$(HERM) Go.hss resume

bare:
	$(HERM)

compile-mono:
	cd .. ; make

compile-circat:
	cd ~/Tabula/Haskell/circat ; make

compile-extras:
	cd ~/Tabula/Haskell/hermit-extras ; make

compile-all: compile-circat compile-extras compile-mono

# doit:
# 	time $(HERM) Go.hss resume && ./Example

# reify-done:
# 	echo "" | make reify ; echo

# no-reify-done:
# 	echo "" | make no-reify ; echo

# dont-done:
# 	echo "" | make dont ; echo

# foo-done:
# 	echo "" | make foo ; echo

# reify:
# 	$(HERM) Go.hss

# no-reify:
# 	$(HERM) GoNoReify.hss

# dont:
# 	$(HERM) Dont.hss

# foo:
# 	$(HERM) Foo.hss

# compile:
# 	cd ../..; make

