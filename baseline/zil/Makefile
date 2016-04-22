OCB := ocamlbuild -use-ocamlfind
PROVE := prove

################################################################################

defaul: byte

all: byte native plugin top doc test

byte: zil.cma

native: zil.cmxa

plugin: zil.cmxs

top: zil_top.top

doc: zil.docdir/index.html

################################################################################

zil.cma zil.cmxa zil.cmxs:
	$(OCB) $@

zil_top.top:
	$(OCB) $@

zil.docdir/index.html:
	$(OCB) -docflag -charset -docflag utf8 $@

################################################################################

T := $(patsubst t/%.ml,%,$(wildcard t/*.ml))

$(T):%:
	@echo '#' $*
	@$(OCB) -quiet t/$*.byte --

test: $(T)

prove:
	@$(PROVE) -e "make" $(T)

################################################################################

clean:
	$(OCB) -clean

.PHONY: default lib top doc zil.cma zil_top.top zil.docdir/index.html clean test $(T)

dump-%:
	@echo $* = $($*)
